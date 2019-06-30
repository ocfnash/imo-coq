Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Import ListNotations.

From q3_2001 Require Export misc.
From q3_2001 Require Export nat_list_max.
From q3_2001 Require Export ceil.
From q3_2001 Require Export inequalities.
From q3_2001 Require Export list_extra.
From q3_2001 Require Export matrices.

Section Question.

  Variables (r : nat) (M : matrix nat r).

  Definition c := col_count M.
  Definition m := nat_list_max (map nunique (columns M)).
  Definition n := nat_list_max (map nunique (rows M)).
  Definition k := k' r c m n.

  Definition is_good (v : list nat) (x : nat) := k <=? count_occ Nat.eq_dec v x.
  Definition is_bad (v : list nat) (x : nat) := negb (is_good v x).
  Definition is_both_good (vwx : list nat * list nat * nat) :=
    match vwx with | (v, w, x) => is_good v x && is_good w x end.
  Definition is_either_bad (vwx : list nat * list nat * nat) :=
    match vwx with | (v, w, x) => is_bad v x || is_bad w x end.

  Lemma is_bad_spec : forall (v : list nat),
    let f := fun x => count_occ Nat.eq_dec v x <? k in
      forall x, f x = is_bad v x.
  Proof.
    intros v f x. unfold f. unfold is_bad. unfold is_good.
    destruct (Nat.leb_spec0 k (count_occ Nat.eq_dec v x)) as [Hx | Hx]; simpl.
    - rewrite Nat.ltb_ge. assumption.
    - rewrite Nat.ltb_lt. omega.
  Qed.

  Lemma m_spec : forall v, In v (columns M) -> nunique v <= m.
  Proof. intros v Hv. unfold m. apply nat_list_max_spec_3. apply in_map. assumption. Qed.

  Lemma n_spec : forall v, In v (rows M) -> nunique v <= n.
  Proof. intros v Hv. unfold n. apply nat_list_max_spec_3. apply in_map. assumption. Qed.

  Lemma is_either_bad_spec : forall (x : nat) (v w : list nat),
    is_either_bad (v, w, x) = false <-> is_both_good (v, w, x) = true.
  Proof.
    intros x v w.
    unfold is_either_bad. unfold is_both_good. unfold is_bad.
    rewrite -> Bool.orb_false_iff. repeat (rewrite -> Bool.negb_false_iff). rewrite Bool.andb_true_iff.
    reflexivity.
  Qed.

  Lemma mn_non_zero : r <> 0 -> c <> 0 -> m <> 0 /\ n <> 0.
  Proof.
    intros Hr Hc.
    unfold m. unfold n.
    split; intros contra; rewrite nat_list_max_spec_4 in contra.
    - assert (H : forall v, ~In v (columns M)). {
        intros v Hv.
        specialize (contra (nunique v) (in_map nunique (columns M) v Hv)).
        apply nunique_spec_5 in contra.
        apply columns_spec_0 in Hv.
        rewrite contra in Hv. simpl in Hv. symmetry in Hv. contradiction.
      }
      apply list_in_nil in H.
      unfold c in Hc. unfold col_count in Hc. rewrite H in Hc. simpl in Hc. contradiction.
    - assert (H : forall v, ~In v (rows M)). {
        intros v Hv.
        specialize (contra (nunique v) (in_map nunique (rows M) v Hv)).
        apply nunique_spec_5 in contra.
        apply columns_spec_0 in Hv.
        rewrite contra in Hv. simpl in Hv. symmetry in Hv. contradiction.
      }
      apply list_in_nil in H.
      rewrite <- (rows_spec_1 M) in Hr. rewrite H in Hr. simpl in Hr. contradiction.
  Qed.

  Lemma single_col_bad_count : r <> 0 -> c <> 0 -> forall v, In v (columns M) ->
    length (filter (is_bad v) v) <= (m-1) * (k-1).
  Proof.
    intros Hr Hc v Hv. destruct v as [| x v]; [apply Nat.le_0_l|].
    rewrite <- (filter_ext _ _ _ (is_bad_spec (x::v))). apply list_length_nunique_php.
    - discriminate.
    - apply m_spec. assumption.
    - rewrite -> (columns_spec_0 M (x::v) Hv).
      apply k_spec_2; try (apply mn_non_zero); assumption.
  Qed.

  Lemma single_row_bad_count : r <> 0 -> c <> 0 -> forall v, In v (rows M) ->
    length (filter (is_bad v) v) <= (n-1) * (k-1).
  Proof.
    intros Hr Hc v Hv. destruct v as [| x v]; [apply Nat.le_0_l|].
    rewrite <- (filter_ext _ _ _ (is_bad_spec (x::v))). apply list_length_nunique_php.
    - discriminate.
    - apply n_spec. assumption.
    - rewrite -> (rows_spec_0 M (x::v) Hv).
      apply k_spec_3; try (apply mn_non_zero); assumption.
  Qed.

  Lemma col_bad_count : r <> 0 -> c <> 0 ->
    let is_col_bad := fun (vwx : list nat * list nat * nat) => match vwx with | (v, w, x) => is_bad w x end in
      length (filter_columnwise is_col_bad (matrix_by_row_and_column M)) <= c * ((m-1) * (k-1)).
  Proof.
    intros Hr Hc is_col_bad.
    unfold c. rewrite <- matrix_by_row_and_column_spec_0.
    apply filter_columnwise_bounded_length.
    intros u Hu.
    pose (w' := (map snd u)).
    rewrite <- map_length with (f:=snd) (l:=(filter is_col_bad u)).
    rewrite <- filter_map_commute with (fB:=(is_bad w')).
    - apply matrix_by_row_and_column_spec_4 in Hu. fold w' in Hu. fold w'. apply single_col_bad_count; assumption.
    - intros [[v w] x] Hvwx. simpl. apply (matrix_by_row_and_column_spec_2 M u) in Hvwx.
      + subst. fold w'. reflexivity.
      + assumption.
  Qed.

  Lemma row_bad_count : r <> 0 -> c <> 0 ->
    let is_row_bad := fun (vwx : list nat * list nat * nat) => match vwx with | (v, w, x) => is_bad v x end in
      length (filter_rowwise is_row_bad (matrix_by_row_and_column M)) <= r * ((n-1) * (k-1)).
  Proof.
    intros Hr Hc is_row_bad.
    apply filter_rowwise_bounded_length.
    intros u Hu.
    pose (v' := (map snd u)).
    rewrite <- map_length with (f:=snd) (l:=(filter is_row_bad u)).
    rewrite <- filter_map_commute with (fB:=(is_bad v')).
    - apply matrix_by_row_and_column_spec_5 in Hu. fold v'. apply single_row_bad_count; assumption.
    - intros [[v w] x] Hvwx. simpl. apply (matrix_by_row_and_column_spec_3 M u) in Hvwx.
      + subst. fold v'. reflexivity.
      + assumption.
  Qed.

  Lemma either_bad_count : r <> 0 -> c <> 0 ->
    length (filter_columnwise is_either_bad (matrix_by_row_and_column M)) < r*c.
  Proof.
    intros Hr Hc.
    destruct (mn_non_zero Hr Hc) as [Hm Hn].
    pose (is_row_bad := (fun (vwx : list nat * list nat * nat) => match vwx with | (v, w, x) => is_bad v x end)).
    pose (is_col_bad := (fun (vwx : list nat * list nat * nat) => match vwx with | (v, w, x) => is_bad w x end)).
    assert (H : forall vwx, is_either_bad vwx = (orf is_row_bad is_col_bad) vwx). { intros [[v w] x]. reflexivity. }
    apply filter_ext with (l := (flatten_columnwise (matrix_by_row_and_column M))) in H.
    unfold filter_columnwise. rewrite -> H.
    assert (Hr' : length (filter_columnwise is_row_bad (matrix_by_row_and_column M)) <= r * ((n - 1) * (k - 1))). {
      rewrite <- filter_columnwise_rowwise_same_length. apply row_bad_count; assumption. }
    assert (Hc' : length (filter_columnwise is_col_bad (matrix_by_row_and_column M)) <= c * ((m - 1) * (k - 1))). {
      apply col_bad_count; assumption. }
    assert (Hrc : length (filter (orf is_row_bad is_col_bad) (flatten_columnwise (matrix_by_row_and_column M))) <=
                  length (filter_columnwise is_row_bad (matrix_by_row_and_column M)) +
                  length (filter_columnwise is_col_bad (matrix_by_row_and_column M))). {
      apply list_filter_disjunction_length.
    }
    pose (Hk := (k_spec_5 _ _ _ _ Hr Hc Hm Hn)). fold k in Hk. omega.
  Qed.

  Theorem php_2d : r <> 0 -> c <> 0 -> exists x v w i j,
    nth_error (rows M) i = Some v /\
    nth_error (columns M) j = Some w /\
    nth_error w i = Some x /\
    nth_error v j = Some x /\
    k <= count_occ Nat.eq_dec v x /\
    k <= count_occ Nat.eq_dec w x.
  Proof.
    intros Hr Hc.
    apply either_bad_count in Hr; [| assumption].
    unfold c in Hr. apply matrix_filter_by_row_and_column_spec_0 in Hr.
    destruct Hr as [x [v [w [j [Hv [Hj [Hj' Hvwx]]]]]]].
    apply In_nth_error in Hv. destruct Hv as [i Hi].
    assert (Hij : nth_error w i = Some x). { rewrite (matrix_indexing_commutes M i j Hj Hi) in Hj'. assumption. }
    exists x. exists v. exists w. exists i. exists j.
    repeat (rewrite <- Nat.leb_le).
    fold (is_good v x). fold (is_good w x).
    rewrite <- Bool.andb_true_iff.
    fold (is_both_good (v, w, x)).
    rewrite <- is_either_bad_spec. tauto.
  Qed.

End Question.
