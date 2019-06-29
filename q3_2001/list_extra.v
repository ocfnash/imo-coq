Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Import ListNotations.

From q3_2001 Require Export misc.
From q3_2001 Require Export ceil.
From q3_2001 Require Export nunique.
From q3_2001 Require Export mode.
From q3_2001 Require Export value_counts.

Lemma php : forall (l : list nat) (x : nat), mode l = Some x ->
  ceil (length l) (nunique l) <= count_occ Nat.eq_dec l x.
Proof.
  intros l x Hx.
  pose (H_len:=(count_occ_nodup l)). rewrite H_len.
  apply largest_elt_spec_7.
  unfold mode in Hx. assumption.
Qed.

Lemma list_filter_exhaustive : forall {A : Type} (f : A -> bool) (l : list A),
  let nf := compose negb f in
    length (filter f l) + length (filter nf l) = length l.
Proof.
  intros A f. induction l as [| x l IHl]; intros nf; [reflexivity|].
  destruct (f x) eqn:Hfx; simpl; unfold nf at 1; unfold compose;
  rewrite -> Hfx; simpl; [| rewrite -> Nat.add_succ_r]; apply eq_S; assumption.
Qed.

Corollary list_filter_exhaustive' : forall {A : Type} (f : A -> bool) (l : list A),
  length (filter f l) < length l -> exists x, In x l /\ f x = false.
Proof.
  intros A f l Hf.
  assert (Hnf : length (filter (compose negb f) l) <> 0). {
    rewrite <- (list_filter_exhaustive f l) in Hf. omega.
  }
  rewrite <- list_non_empty_iff_length_non_zero in Hnf.
  rewrite filter_non_empty_spec in Hnf.
  unfold compose in Hnf. destruct Hnf as [x Hx]. exists x.
  rewrite -> Bool.negb_true_iff in Hx. assumption.
Qed.

Lemma nunique_filter_exhaustive : forall (f : nat -> bool) (l : list nat),
  nunique (filter f l) + nunique (filter (negf f) l) = nunique l.
Proof.
  intros f. induction l as [| x l IHl]; try reflexivity.
  destruct (f x) eqn:Hfx; destruct (in_dec Nat.eq_dec x l) as [Hx|Hx].
  (* Urgh, here we go with case analysis :/ *)
  - (* f x = true /\ In x l *)
    assert (Hfx' : (negf f) x = false). { rewrite <- negf_spec_0. assumption. }
    assert (Hx' : In x (filter f l)). { rewrite filter_In. split; assumption. }
    simpl. rewrite -> Hfx.
    simpl. rewrite -> Hfx'.
    rewrite (nunique_spec_3 _ _ Hx). rewrite (nunique_spec_3 _ _ Hx'). assumption.
  - (* f x = true /\ ~In x l *)
    assert (Hfx' : (negf f) x = false). { rewrite <- negf_spec_0. assumption. }
    assert (Hx' : ~In x (filter f l)). { intros contra. rewrite filter_In in contra. destruct contra as [H _]. contradiction. }
    simpl. rewrite -> Hfx.
    simpl. rewrite -> Hfx'.
    rewrite (nunique_spec_4 _ _ Hx). rewrite (nunique_spec_4 _ _ Hx'). rewrite <- IHl. omega.
  - (* f x = false /\ In x l *)
    assert (Hfx' : (negf f) x = true). { rewrite <- negf_spec_1. assumption. }
    assert (Hx' : In x (filter (negf f) l)). { rewrite filter_In. split; assumption. }
    simpl. rewrite -> Hfx.
    simpl. rewrite -> Hfx'.
    rewrite (nunique_spec_3 _ _ Hx). rewrite (nunique_spec_3 _ _ Hx'). assumption.
  - (* f x = false /\ ~In x l *)
    assert (Hfx' : (negf f) x = true). { rewrite <- negf_spec_1. assumption. }
    assert (Hx' : ~In x (filter (negf f) l)). { intros contra. rewrite filter_In in contra. destruct contra as [H _]. contradiction. }
    simpl. rewrite -> Hfx.
    simpl. rewrite -> Hfx'.
    rewrite (nunique_spec_4 _ _ Hx). rewrite (nunique_spec_4 _ _ Hx'). rewrite <- IHl. omega.
Qed.

Lemma nunique_filter : forall (f : nat -> bool) (l : list nat),
  (exists x, In x l /\ f x = false) <-> nunique (filter f l) < nunique l.
Proof.
  intros f l.
  assert (H1 : nunique (filter f l) < nunique l <-> nunique (filter (negf f) l) <> 0). {
    rewrite <- (nunique_filter_exhaustive f l). omega.
  }
  rewrite -> H1. rewrite -> nunique_spec_2. rewrite filter_non_empty_spec.
  unfold negf. split; intros [x Hx]; exists x.
  - rewrite -> Bool.negb_true_iff. assumption.
  - rewrite -> Bool.negb_true_iff in Hx. assumption.
Qed.

Lemma length_nunique_max_freq : forall (l : list nat) (k : nat),
  (forall x, count_occ Nat.eq_dec l x <= k) -> length l <= (nunique l) * k.
Proof.
  intros l k Hk.
  destruct (mode l) as [y|] eqn:mode_l.
  - (* mode l = Some y *)
    assert (H : length l <= (nunique l) * (count_occ Nat.eq_dec l y)). {
       pose (H_len:=(count_occ_nodup l)). rewrite H_len. rewrite nunique_spec_0.
       apply largest_elt_spec_5. assumption.
    }
    specialize Hk with (x:=y).
    apply Nat.mul_le_mono_l with (p:=(nunique l)) in Hk. omega.
  - (* mode l = None *)
    rewrite mode_spec_0 in mode_l. subst. auto.
Qed.

Corollary length_nunique_max_freq' : forall (l : list nat) (k m : nat),
  nunique l <= m -> (forall x, count_occ Nat.eq_dec l x <= k) -> length l <= m * k.
Proof.
  intros l k m Hm Hk.
  apply length_nunique_max_freq in Hk.
  apply Nat.mul_le_mono_r with (p:=k) in Hm.
  omega.
Qed.

Lemma freq_filter : forall (l : list nat) (f : nat -> bool) (x : nat),
  count_occ Nat.eq_dec (filter f l) x <= count_occ Nat.eq_dec l x.
Proof.
  induction l as [| y l IHl]; intros f x.
  - simpl. apply le_n.
  - destruct (f y) eqn:Hy; simpl; rewrite Hy;
    destruct (Nat.eq_dec y x) as [Hxy | Hxy].
    + rewrite Hxy. rewrite count_occ_cons_eq; try reflexivity. apply le_n_S. apply IHl.
    + rewrite count_occ_cons_neq; try assumption. apply IHl.
    + apply le_S. apply IHl.
    + apply IHl.
Qed.

Lemma list_length_nunique_php : forall (p q : nat) (l : list nat),
  let f := (fun x => count_occ Nat.eq_dec l x <? q) in
    l <> [] -> nunique l <= p -> q <= ceil (length l) p ->
    length (filter f l) <= (p-1)*(q-1).
Proof.
  intros p q l f Hl Hp Hq.
  rewrite <- nunique_spec_1 in Hl.
  assert (H1 : ceil (length l) p <= ceil (length l) (nunique l)). {
    apply ceil_spec_4; (try assumption); (try reflexivity).
  }
  assert (H2 : exists x, In x l /\ f x = false). {
    destruct (mode l) as [x|] eqn:mode_x.
    - (* mode l = Some x *)
      exists x. split.
      + apply mode_spec_3 in mode_x. assumption.
      + apply php in mode_x. unfold f. rewrite -> Nat.ltb_ge. omega.
    - (* mode l = None : cannot actually happen since l is non-empty *)
      exfalso. rewrite mode_spec_0 in mode_x. subst. apply Hl. auto.
  }
  assert (H3 : nunique (filter f l) <= p-1). {
    rewrite -> nunique_filter in H2. omega.
  }
  apply length_nunique_max_freq'; try assumption.
  intros x. destruct (in_dec Nat.eq_dec x (filter f l)) as [H_in | H_in].
  - (* In x (filter f l) *)
    rewrite -> filter_In in H_in. destruct H_in as [_ Hx].
    unfold f in Hx. rewrite -> Nat.ltb_lt in Hx. assert (Hx' : count_occ Nat.eq_dec l x <= q-1). { omega. }
    apply (le_trans _ _ _ (freq_filter l f x) Hx').
  - (* ~In x (filter f l *)
    rewrite -> (count_occ_not_In Nat.eq_dec) in H_in. rewrite -> H_in. apply Nat.le_0_l.
Qed.

Lemma filter_subset_length : forall {A : Type} (l : list A) (f g : A -> bool),
  (forall x, f x = true -> g x = true) -> length (filter f l) <= length (filter g l).
Proof.
  induction l as [| x l IHl]; try auto.
  intros f g H_fg. destruct (f x) eqn:Hx.
  - assert (Hx' : g x = true). { apply H_fg. assumption. }
    simpl. rewrite -> Hx. rewrite -> Hx'. simpl. rewrite <- Nat.succ_le_mono.
    apply IHl. assumption.
  - simpl. rewrite -> Hx. destruct (g x) eqn: Hx'.
    + simpl. apply le_S. apply IHl. assumption.
    + apply IHl. assumption.
Qed.

Lemma list_filter_disjunction_length : forall {A : Type} (f g : A -> bool) (l : list A),
  length (filter (orf f g) l) <= length (filter f l) + length (filter g l).
Proof.
  intros A f g. induction l as [| x l IHl]; [auto|].
  destruct (f x) eqn:Hfx; destruct (g x) eqn:Hgx; simpl;
  unfold orf at 1; rewrite -> Hfx; rewrite -> Hgx; simpl; omega.
Qed.

Lemma concat_length : forall {A : Type} (l : list (list A)) (n : nat),
  (forall v, In v l -> length v <= n) -> length (concat l) <= (length l) * n.
Proof.
  intros A. induction l as [| m l IHl]; intros n Hn; [auto|].
  simpl. rewrite -> app_length.
  assert (Hn1 : length m <= n). { apply Hn. left. reflexivity. }
  assert (Hn2 : forall v, In v l -> length v <= n). { intros v Hv. apply Hn. right. assumption. }
  apply IHl in Hn2. omega.
Qed.

Lemma concat_filter_length : forall {A : Type}
  (l : list (list A))
  (f : A -> bool)
  (b : nat)
  (evBoundedLength : forall v, In v l -> length (filter f v) <= b),
    length (filter f (concat l)) <= (length l) * b.
Proof.
  intros A l f b evBoundedLength.
  rewrite <- concat_filter_map.
  pose (vfs := (map (filter f) l)).
  assert (Hlen : length vfs = length l). { apply map_length. }
  rewrite <- Hlen. apply (concat_length vfs b).
  intros vf Hvf. unfold vfs in Hvf. rewrite -> in_map_iff in Hvf.
  destruct Hvf as [v [Hvf Hv]]. rewrite <- Hvf.
  apply evBoundedLength; assumption.
Qed.

Lemma split_fst_snd : forall {A B : Type} (l : list (A * B)),
  split l = (map fst l, map snd l).
Proof.
  intros A B. induction l as [| [x y] l IHl]; [auto|].
  simpl. rewrite IHl. reflexivity.
Qed.

(* This seems ridiculous: there must be a tactic to abstract this more generally. *)
Lemma map_Some_eq : forall {A : Type} (l l' : list A),
  l = l' <-> map Some l = map Some l'.
Proof.
  intros A l l'. split.
  - intros H. rewrite H. reflexivity.
  - generalize dependent l'. induction l as [| x l IHl]; simpl; intros l' H.
    + symmetry in H. apply map_eq_nil in H. auto.
    + destruct l' as [| x' l']; [discriminate|].
      simpl in H. inversion H.
      apply IHl in H2. subst.
      reflexivity.
Qed.

Lemma map_option_commuting : forall {A B C : Type} (l : list A) (l' : list B) (f : A -> option C) (g : B -> C) (h : A -> option B),
  (forall a b, h a = Some b -> f a = Some (g b)) -> map h l = map Some l' -> map f l = map Some (map g l').
Proof.
  intros A B C. induction l as [| x l IHl]; intros l' f g h H; intros H'.
  - simpl in H'. symmetry in H'. apply map_eq_nil in H'. subst. reflexivity.
  - destruct l' as [|x' l']; simpl in H'; [discriminate|].
    inversion H'. simpl. apply H in H1. rewrite H1.
    apply IHl with (l':=l') in H.
    + rewrite H. reflexivity.
    + assumption.
Qed.

Lemma combine_fst : forall {A B : Type} (l : list A) (l' : list B),
  length l <= length l' -> map fst (combine l l') = l.
Proof.
  intros A B l l' H.
  rewrite combine_firstn_l; [| assumption].
  assert (Hlen : length l = length (firstn (length l) l')). { apply firstn_length_le in H. auto. }
  apply combine_split in Hlen.
  rewrite split_fst_snd in Hlen.
  injection Hlen. firstorder.
Qed.

Lemma combine_snd : forall {A B : Type} (l : list A) (l' : list B),
  length l' <= length l -> map snd (combine l l') = l'.
Proof.
  intros A B l l' H.
  rewrite combine_firstn_r; [| assumption].
  assert (Hlen : length l' = length (firstn (length l') l)). { apply firstn_length_le in H. auto. }
  symmetry in Hlen. apply combine_split in Hlen.
  rewrite split_fst_snd in Hlen.
  injection Hlen. firstorder.
Qed.

Lemma map_nth_error' : forall {A B : Type} (f : A -> B) (l : list A) (y : B) (n : nat),
  nth_error (map f l) n = Some y -> (exists x : A, f x = y /\ nth_error l n = Some x).
Proof.
  intros A B f l y n H.
  assert (Hlen : n < length l). {
    rewrite <- map_length with (f:=f).
    rewrite <- nth_error_Some.
    rewrite H.
    intros contra; discriminate.
  }
  assert (H' : exists x, nth_error l n = Some x). {
    apply nth_error_Some in Hlen. destruct (nth_error l); [eauto | contradiction].
  }
  destruct H' as [x Hx].
  exists x. split.
  - apply map_nth_error with(f:=f) in Hx. rewrite H in Hx. inversion Hx. reflexivity.
  - assumption.
Qed.

Lemma combine_nth_error' : forall {A B : Type} (l : list A) (l' : list B) (n : nat) (ab : A*B),
  length l = length l' -> nth_error (combine l l') n = Some ab -> nth_error l n = Some (fst ab) /\ nth_error l' n = Some (snd ab).
Proof.
  intros A B l l' n [a b] Hlen H. simpl.
  assert (H' : nth_error (combine l l') n <> None). { rewrite H. discriminate. }
  assert (Hlen_l : n < length l). {
    apply nth_error_Some in H'. rewrite combine_length in H'. apply Nat.min_glb_lt_iff in H'.
    destruct H' as [H' _]. assumption.
  }
  assert (Hlen_l' : n < length l'). {
    apply nth_error_Some in H'. rewrite combine_length in H'. apply Nat.min_glb_lt_iff in H'.
    destruct H' as [_ H']. assumption.
  }
  apply nth_error_nth in H. split;
  apply combine_split in Hlen;
  rewrite split_nth in H; repeat (rewrite Hlen in H); simpl in H; inversion H;
  apply nth_error_nth'; assumption.
Qed.

Lemma firstn_nth_error : forall {A : Type} (l : list A) (n : nat),
  nth_error l n = nth_error (firstn (n+1) l) n.
Proof.
  intros A l n.
  destruct (Nat.leb_spec0 (n+1) (length l)) as [H | H].
  - rewrite <- firstn_skipn with (n:= (n+1)) (l:=l) at 1.
    apply nth_error_app1. apply firstn_length_le in H. omega.
  - assert (Hl : length l <= n). { omega. }
    assert (Hr : length (firstn (n+1) l) <= n). { rewrite firstn_all2; omega. }
    apply nth_error_None in Hl. rewrite Hl.
    apply nth_error_None in Hr. rewrite Hr.
    reflexivity.
Qed.

Lemma combine_nth_error : forall {A B : Type} (l : list A) (l' : list B) (n : nat) (ab : A*B),
  nth_error (combine l l') n = Some ab -> nth_error l n = Some (fst ab) /\ nth_error l' n = Some (snd ab).
Proof.
  intros A B l l' n ab H. simpl.
  assert (Hn1 : n < length l). {
    assert (H' : nth_error (combine l l') n <> None). { rewrite H. discriminate. }
    apply nth_error_Some in H'.
    rewrite combine_length in H'.
    apply Nat.min_glb_lt_iff in H'.
    destruct H' as [H' _]. assumption.
  }
  assert (Hn2 : n < length l'). {
    assert (H' : nth_error (combine l l') n <> None). { rewrite H. discriminate. }
    apply nth_error_Some in H'.
    rewrite combine_length in H'.
    apply Nat.min_glb_lt_iff in H'.
    destruct H' as [_ H']. assumption.
  }
  pose (m := (firstn (n+1) l)).
  pose (m' := (firstn (n+1) l')).
  assert (Hm : length m = n+1). { apply firstn_length_le. omega. }
  assert (Hm' : length m' = n+1). { apply firstn_length_le. omega. }
  assert (Hmm : combine m m' = firstn (n+1) (combine l l')). {
    rewrite combine_firstn; auto; omega.
  }
  rewrite (firstn_nth_error l). rewrite (firstn_nth_error l').
  apply combine_nth_error'; fold m; fold m'.
  - rewrite Hm. rewrite Hm'. reflexivity.
  - rewrite Hmm. rewrite <- firstn_nth_error. assumption.
Qed.

Definition combine_lists {A : Type} (v : list A) (l : list (list A)) : list (list A) :=
  map (prod_curry cons) (combine v l).

Lemma combine_lists_spec_0 : forall {A : Type} (w : list A),
  combine_lists w [] = [].
Proof.
  intros A w.
  unfold combine_lists.
  apply list_in_nil.
  intros a.
  rewrite in_map_iff.
  intros [xw [H H']].
  rewrite combine_nil in H'.
  apply in_nil in H'.
  contradiction.
Qed.

Lemma combine_lists_spec_1 : forall {A : Type} (w v : list A) (l : list (list A)),
  In v (combine_lists w l) -> length v <> 0.
Proof.
  intros A w v l H.
  unfold combine_lists in H.
  rewrite in_map_iff in H. destruct H as [[x v'] [H _]]. simpl in H.
  rewrite <- H. simpl. discriminate.
Qed.

Lemma nth_error_combine_lists : forall {A : Type} (w v : list A) (x : A) (l : list (list A)) (i : nat),
  nth_error (combine_lists w l) i = Some (x::v) -> nth_error w i = Some x /\ nth_error l i = Some v.
Proof.
  intros A w v x l i H.
  assert (H' : nth_error (combine w l) i = Some (x, v)). {
    unfold combine_lists in H.
    apply map_nth_error' in H. destruct H as [[x' v'] [H H']].
    inversion H. subst. assumption.
  }
  apply combine_nth_error in H'. auto.
Qed.

Definition transpose_lists {A : Type} (l : list (list A)) (r : nat) : list (list A) :=
  fold_right combine_lists (repeat [] r) l.

Lemma transpose_lists_spec_0 : forall {A : Type} (l : list (list A)) (r : nat),
  (forall v, In v l -> length v = r) -> length (transpose_lists l r) = r.
Proof.
  intros A. induction l as [| v l IHl]; intros r Hr; simpl.
  - apply repeat_length.
  - unfold combine_lists. rewrite map_length. rewrite combine_length.
    assert (Hv : length v = r). { apply Hr. left. reflexivity. }
    assert (Hl : length (transpose_lists l r) = r). {
      apply IHl. intros v' Hv'. apply Hr. right. assumption. }
    rewrite Hv, Hl. apply Nat.min_id.
Qed.

Lemma transpose_lists_spec_1 : forall {A : Type} (l : list (list A)) (r : nat) (v : list A),
  In v (transpose_lists l r) -> length v = length l.
Proof.
  intros A. induction l as [| v' l IHl]; intros r v Hv.
  - simpl in Hv. apply repeat_spec in Hv. subst. reflexivity.
  - simpl. unfold transpose_lists in Hv. simpl in Hv.
    unfold combine_lists in Hv. rewrite in_map_iff in Hv.
    destruct Hv as [[a w] [H H']]. simpl in H. apply in_combine_r in H'.
    subst. simpl. apply eq_S. apply IHl with (r:=r).
    unfold transpose_lists. unfold combine_lists. assumption.
Qed.

Lemma combine_lists_permutation_induct : forall {A : Type} (l : list (list A)) (v : list A),
  length l = length v -> Permutation (concat (combine_lists v l)) (v++(concat l)).
Proof.
  induction l as [| v' l IHl]; simpl; intros v HLen.
  - symmetry in HLen. apply length_zero_iff_nil in HLen. subst. simpl. apply perm_nil.
  - destruct v as [| x v]; inversion HLen.
    simpl.
    apply perm_trans with (l':=(x :: v' ++ v ++ concat l)).
    + apply perm_skip. apply Permutation_app_head. apply IHl. assumption.
    + apply perm_skip. repeat (rewrite -> app_assoc). apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
