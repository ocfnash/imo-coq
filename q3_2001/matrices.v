Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Import ListNotations.

From q3_2001 Require Export misc.
From q3_2001 Require Export list_extra.

Set Implicit Arguments.

Section Matrices.

  Variables (A : Type).

  Inductive matrix (r : nat) := (* TODO Can we use a Record for this? *)
    | make_matrix : forall (l : list (list A))
                           (evConstLengthCols : forall v, In v l -> length v = r), matrix r.

  Definition columns {r : nat} (M : matrix r) : list (list A) :=
    match M with
    | make_matrix l _ => l
    end.

  Lemma columns_spec_0 : forall {r : nat} (M : matrix r) (v : list A),
    In v (columns M) -> length v = r.
  Proof. intros r [cols evLen] v Hv. simpl in Hv. apply evLen in Hv. assumption. Qed.

  Definition add_column {r : nat} (M : matrix r) (v : list A) (evLenV : length v = r) : matrix r.
  refine (make_matrix (v::(columns M)) _).
    intros v' Hv'.
    apply in_inv in Hv'. destruct Hv'.
    - rewrite H in evLenV. assumption.
    - apply columns_spec_0 in H. assumption.
  Defined.

  Definition col_count {r : nat} (M : matrix r) : nat :=
    length (columns M).

  Definition transpose {r : nat} (M : matrix r) : matrix (col_count M).
    refine (make_matrix (transpose_lists (columns M) r) _).
    apply transpose_lists_spec_1.
  Defined.

  Definition rows {r : nat} (M : matrix r) : list (list A) :=
    columns (transpose M).

  Lemma rows_spec_0 : forall {r : nat} (M : matrix r) (v : list A),
    In v (rows M) -> length v = col_count M.
  Proof. intros r M v Hv. unfold rows in Hv. apply columns_spec_0 in Hv. assumption. Qed.

  Lemma rows_spec_1 : forall {r : nat} (M : matrix r),
    length (rows M) = r.
  Proof.
    unfold rows. unfold transpose. simpl. intros r M.
    apply transpose_lists_spec_0. apply columns_spec_0.
  Qed.

  Lemma rows_spec_5 : forall {r : nat} (M : matrix r) (v : list A) (i : nat),
    nth_error (rows M) i = Some v -> map (fun w => nth_error w i) (columns M) = map Some v.
  Proof.
    unfold rows. unfold transpose. unfold transpose_lists.
    intros r [l Hl]. induction l as [| w l IHl]; intros v i Hv;
    simpl; simpl in Hv.
    - apply nth_error_In in Hv. apply repeat_spec in Hv. rewrite Hv. reflexivity.
    - destruct v as [|x v]; simpl; simpl in IHl.
      + exfalso. apply nth_error_In in Hv. apply combine_lists_spec_1 in Hv.
        simpl in Hv. contradiction.
      + apply nth_error_combine_lists in Hv. destruct Hv as [Hx Hv].
        rewrite IHl with (v:=v).
        * rewrite Hx. reflexivity.
        * intros v' Hv'. apply Hl. apply in_cons. assumption.
        * assumption.
  Qed.

  Lemma rows_spec_2 : forall {r : nat} (M : matrix r) (v w : list A) (x : A),
    In w (columns M) -> In (v, x) (combine (rows M) w) -> In x v.
  Proof.
    intros r [l Hl] v w x Hw Hvx.
    apply In_nth_error in Hvx. destruct Hvx as [i Hi].
    apply combine_nth_error in Hi. simpl in Hi. destruct Hi as [Hvi Hxi].
    apply rows_spec_5 in Hvi.
    apply in_map with (f:=(fun w' => nth_error w' i)) in Hw.
    rewrite Hxi in Hw. rewrite Hvi in Hw.
    rewrite in_map_iff in Hw. destruct Hw as [y [Hy Hy']].
    inversion Hy. subst. assumption.
  Qed.

  Lemma rows_spec_3 : forall {r : nat} (M : matrix r) (v : list A) (evLenV : length v = r),
    rows (add_column M v evLenV) = combine_lists v (rows M).
  Proof. intros r [l Hl] v Hv. reflexivity. Qed.

  Lemma rows_spec_4 : forall {r : nat} (M : matrix r) (v : list A),
    In v (rows M) -> exists i, map (fun w => nth_error w i) (columns M) = map Some v.
  Proof.
    intros r M v Hv.
    apply In_nth_error in Hv. destruct Hv as [i Hi].
    exists i.
    apply rows_spec_5. assumption.
  Qed.

  Definition matrix_in (x : A) {r : nat} (M : matrix r) :=
    In x (concat (columns M)).

  Lemma matrix_in_spec : forall {r : nat} (M : matrix r) (x : A),
    matrix_in x M <-> exists v, In v (columns M) /\ In x v.
  Proof. unfold matrix_in. intros r M x. apply concat_In. Qed.

  Definition ijth_error {r: nat} (M : matrix r) (i j : nat) :=
    match (nth_error (columns M) j) with
    | Some w => nth_error w i
    | _ => None
    end.

  Lemma ijth_error_In : forall {r: nat} (M : matrix r) (i j : nat) (x : A),
    ijth_error M i j = Some x -> matrix_in x M.
  Proof.
    intros r M i j x H.
    unfold ijth_error in H.
    destruct (nth_error (columns M) j) as [w|] eqn:Hj; [| discriminate].
    apply nth_error_In in Hj. apply nth_error_In in H.
    rewrite matrix_in_spec.
    exists w. split; assumption.
  Qed.

  Definition ijth_error' {r: nat} (M : matrix r) (i j : nat) :=
    match (nth_error (rows M) i) with
    | Some v => nth_error v j
    | _ => None
    end.

  Lemma ijth_error_transposes : forall {r: nat} (M : matrix r) (i j : nat),
    ijth_error M i j = ijth_error' M i j.
  Proof.
    intros r M i j.
    unfold ijth_error'. unfold ijth_error.
    destruct (nth_error (rows M) i) as [v|] eqn:Hi;
    destruct (nth_error (columns M) j) as [w|] eqn:Hj.
    - apply rows_spec_5 in Hi.
      apply map_nth_error with (f:=(fun w => nth_error w i)) in Hj.
      rewrite Hi in Hj.
      apply map_nth_error' in Hj. destruct Hj as [x [Hx Hx']].
      rewrite <- Hx. rewrite Hx'. reflexivity.
    - apply nth_error_In in Hi. apply rows_spec_0 in Hi. unfold col_count in Hi.
      apply nth_error_None in Hj.
      symmetry. rewrite nth_error_None. rewrite Hi. assumption.
    - apply nth_error_In in Hj. apply columns_spec_0 in Hj.
      apply nth_error_None in Hi. rewrite rows_spec_1 in Hi.
      rewrite nth_error_None. rewrite Hj. assumption.
    - reflexivity.
  Qed.

  Lemma ijth_error_matrix_in : forall {r: nat} (M : matrix r) (x : A),
    matrix_in x M <-> exists i j, ijth_error M i j = Some x.
  Proof.
    intros r M x. split; intros H.
    - unfold matrix_in in H.
      apply concat_In in H. destruct H as [v [Hv Hv']].
      apply In_nth_error in Hv. destruct Hv as [j Hj].
      apply In_nth_error in Hv'. destruct Hv' as [i Hi].
      exists i. exists j.
      unfold ijth_error.
      rewrite Hj. assumption.
    - destruct H as [i [j Hij]].
      unfold ijth_error in Hij.
      destruct (nth_error (columns M) j) as [v|] eqn:Hj.
      + apply nth_error_In in Hj. apply nth_error_In in Hij.
        rewrite matrix_in_spec. exists v. split; assumption.
      + discriminate.
  Qed.

  Lemma matrix_indexing_commutes : forall {r: nat} (M : matrix r) (v w : list A) (i j : nat),
    nth_error (columns M) j = Some w -> nth_error (rows M) i = Some v -> nth_error v j = nth_error w i.
  Proof.
    intros r M v w i j Hj Hi.
    assert (H  : ijth_error  M i j = nth_error w i). { unfold ijth_error.  rewrite Hj. reflexivity. }
    assert (H' : ijth_error' M i j = nth_error v j). { unfold ijth_error'. rewrite Hi. reflexivity. }
    rewrite <- H. rewrite <- H'.
    rewrite ijth_error_transposes. reflexivity.
  Qed.

  Definition flatten_columnwise {r : nat} (M : matrix r) : list A :=
    concat (columns M).

  Lemma flatten_columnwise_spec_0 : forall {r : nat} (M : matrix r) (x : A),
    In x (flatten_columnwise M) <-> matrix_in x M.
  Proof. unfold flatten_columnwise. unfold matrix_in. firstorder. Qed.

  Lemma flatten_columnwise_length : forall {r : nat} (M : matrix r),
    length (flatten_columnwise M) = r * (col_count M).
  Proof.
    intros r [l evLen].
    unfold flatten_columnwise. unfold col_count. simpl.
    induction l as [| v l IHl]; [auto|].
    simpl. rewrite app_length.
    assert (Hl : length (concat l) = r * length l). { apply IHl. intros v' Hv'. apply evLen. apply in_cons. assumption. }
    assert (Hv : length v = r). { apply evLen. apply in_eq. }
    rewrite Hl. rewrite Hv. rewrite <- mult_n_Sm. omega.
  Qed.

  Definition flatten_rowwise {r : nat} (M : matrix r) : list A :=
    concat (rows M).

  Definition filter_columnwise (f : A -> bool) {r : nat} (M : matrix r) : list A :=
    filter f (flatten_columnwise M).

  Definition filter_rowwise (f : A -> bool) {r : nat} (M : matrix r) : list A :=
    filter f (flatten_rowwise M).

  Lemma equal_columns_equal_rows : forall {r : nat} (M M' : matrix r),
    columns M = columns M' -> rows M = rows M'.
  Proof.
    intros r [l evM] [l' evM'] H.
    simpl in H. unfold rows. unfold transpose. simpl. rewrite H. reflexivity.
  Qed.

  Lemma flatten_permutations : forall {r : nat} (M : matrix r),
    Permutation (flatten_rowwise M) (flatten_columnwise M).
  Proof.
    intros r [l evLen]. induction l as [| v l IHl].
    - unfold flatten_rowwise. unfold flatten_columnwise. unfold rows. unfold transpose. simpl.
      assert (H : @concat A (repeat [] r) = []). {
        rewrite concat_nil'. intros m Hm. apply repeat_spec in Hm. assumption.
      }
      rewrite H. apply perm_nil.
    - unfold flatten_rowwise. unfold flatten_columnwise. simpl.
      assert (evLen' : forall v', In v' l -> length v' = r). { intros v' Hv'. apply evLen. apply in_cons. assumption. }
      assert (Hv : length v = r). { apply evLen. apply in_eq. }
      pose (M := (make_matrix l evLen')).
      assert (HM : rows (add_column M v Hv) = rows (make_matrix (v::l) evLen)). { apply equal_columns_equal_rows. auto. }
      pose (H := (rows_spec_3 M v Hv)). rewrite HM in H. rewrite H.
      assert (H' : Permutation (concat (combine_lists v (rows M))) (v++(concat (rows M)))). {
        apply combine_lists_permutation_induct. rewrite Hv. apply rows_spec_1. }
      apply (perm_trans H').
      apply Permutation_app_head.
      specialize (IHl evLen'). unfold flatten_rowwise in IHl. unfold flatten_columnwise in IHl. simpl in IHl. fold M in IHl.
      assumption.
  Qed.

  Corollary matrix_in_spec' : forall {r : nat} (M : matrix r) (x : A),
    matrix_in x M <-> exists v, In v (rows M) /\ In x v.
  Proof.
    intros r M x.
    assert (Hr : In x (flatten_rowwise M) <-> exists v, In v (rows M) /\ In x v). {
      unfold flatten_rowwise. apply concat_In.
    }
    assert (Hc : In x (flatten_columnwise M) <-> exists v, In v (columns M) /\ In x v). {
      unfold flatten_columnwise. apply concat_In.
    }
    rewrite matrix_in_spec. rewrite <- Hr. rewrite <- Hc.
    split; apply Permutation_in; [apply Permutation_sym|]; apply flatten_permutations.
  Qed.

  Lemma filter_columnwise_bounded_length : forall (f : A -> bool) {r : nat} (M : matrix r) (b : nat),
    (forall v, In v (columns M) -> length (filter f v) <= b) -> length (filter_columnwise f M) <= (col_count M) * b.
  Proof.
    intros f r M b Hb.
    unfold filter_columnwise. unfold flatten_columnwise. unfold col_count.
    apply concat_filter_length.
    intros v Hv. apply Hb. assumption.
  Qed.

  Lemma filter_rowwise_bounded_length : forall (f : A -> bool) {r : nat} (M : matrix r) (b : nat),
    (forall v, In v (rows M) -> length (filter f v) <= b) -> length (filter_rowwise f M) <= r * b.
  Proof.
    intros f r M b Hb.
    unfold filter_rowwise. unfold flatten_rowwise. rewrite <- (rows_spec_1 M) at 2.
    apply concat_filter_length.
    intros v Hv. apply Hb. assumption.
  Qed.

  Lemma filter_columnwise_rowwise_same_length : forall (f : A -> bool) {r : nat} (M : matrix r),
    length (filter_rowwise f M) = length (filter_columnwise f M).
  Proof.
    intros f r M.
    unfold filter_rowwise. unfold filter_columnwise.
    apply Permutation_length.
    apply permutation_filter.
    apply flatten_permutations.
  Qed.

End Matrices.


Section MatrixExtra.

  (* This is probably the worst structured part of the codebase (such as it is).
     Three things contributed:

       * Avoiding using numbered indexing of lists (nth_error) for too long.

       * Adding 'spec' lemmata ad hoc rather than initially deciding on a characterising set of specs.

       * The whole idea of matrix_by_row_and_column! It was initally tempting but in restrospect, a
         better approach would have been to introduce a function along the following lines:

            Definition intersect_row_column {r : nat} (M : matrix A r) (v w : list A) (evRow : In v (rows M)) (evCol : In w (columns M)) : A
              := value where v and w intersect (actual cell not uniquely specified but value is unique).

     In any case, lessons learned etc. which was the point of the whole exercise! *)

  Variables (A : Type).

  Definition matrix_by_row_and_column' {r : nat} (M : matrix A r) : list (list ((list A) * (list A) * A)) :=
    map (fun w => map (fun vx => (fst vx, w, snd vx)) (combine (rows M) w)) (columns M).

  Lemma matrix_by_row_and_column'_spec : forall {r : nat} (M : matrix A r) (v : list ((list A) * (list A) * A)),
    In v (matrix_by_row_and_column' M) -> length v = r.
  Proof.
    intros r M v Hv.
    unfold matrix_by_row_and_column' in Hv.
    rewrite in_map_iff in Hv. destruct Hv as [v' [Hv' Hv'_in]].
    assert (H : length v' = r). { apply columns_spec_0 in Hv'_in. assumption. }
    rewrite <- Hv'. rewrite map_length.
    assert (H' : length (rows M) = r). { apply rows_spec_1. }
    rewrite combine_length. rewrite H. rewrite H'. firstorder.
  Qed.

  Definition matrix_by_row_and_column {r : nat} (M : matrix A r) : matrix ((list A) * (list A) * A) r :=
    make_matrix (matrix_by_row_and_column' M) (matrix_by_row_and_column'_spec M).

  Lemma matrix_by_row_and_column_spec_0 : forall {r : nat} (M : matrix A r),
    col_count (matrix_by_row_and_column M) = col_count M.
  Proof.
    intros r M.
    unfold matrix_by_row_and_column. unfold col_count. simpl.
    unfold matrix_by_row_and_column'. rewrite map_length. reflexivity.
  Qed.

  Lemma matrix_by_row_and_column_spec_1 : forall {r : nat} (M : matrix A r) (v w : list A) (x : A),
    matrix_in (v, w, x) (matrix_by_row_and_column M) -> In x v /\ In x w /\ In v (rows M) /\ In w (columns M).
  Proof.
    unfold matrix_by_row_and_column. unfold matrix_by_row_and_column'.
    intros r M v w x Hvwx.
    rewrite matrix_in_spec in Hvwx. destruct Hvwx as [u [Hu Hu']]. simpl in Hu.
    rewrite in_map_iff in Hu. destruct Hu as [x' [H H']]. subst.
    rewrite in_map_iff in Hu'.  destruct Hu' as [[w' x''] [Hwx Hwx']].
    inversion Hwx. subst. repeat split.
    - apply rows_spec_2 in Hwx'; assumption.
    - apply in_combine_r in Hwx'. assumption.
    - apply in_combine_l in Hwx'. assumption.
    - assumption.
  Qed.

  Lemma matrix_by_row_and_column_spec_2 : forall {r : nat} (M : matrix A r) (u : list ((list A) * (list A) * A)) (v w : list A) (x : A),
    In (v, w, x) u -> In u (columns (matrix_by_row_and_column M)) -> w = map snd u.
  Proof.
    unfold matrix_by_row_and_column. unfold matrix_by_row_and_column'. simpl.
    intros r M u v w x Hu Hu'.
    rewrite in_map_iff in Hu'. destruct Hu' as [w' [Hw' Hw'']].
    subst. rewrite map_map. simpl.
    assert (H : snd = fun x : (list A) * A => snd x). { auto. } rewrite <- H.
    assert (Hww : w = w'). {
      rewrite in_map_iff in Hu. destruct Hu as [vx [Hvx Hvx']].
      inversion Hvx. reflexivity.
    }
    rewrite Hww. symmetry.
    apply combine_snd.
    apply columns_spec_0 in Hw''. rewrite rows_spec_1.
    subst. apply le_n.
  Qed.

  Lemma matrix_by_row_and_column_spec_3 : forall {r : nat} (M : matrix A r) (u : list ((list A) * (list A) * A)) (v w : list A) (x : A),
    In (v, w, x) u -> In u (rows (matrix_by_row_and_column M)) -> v = map snd u.
  Proof.
    unfold matrix_by_row_and_column. unfold matrix_by_row_and_column'.
    intros r M u v w x Hu Hu'.
    apply rows_spec_4 in Hu'. destruct Hu' as [i Hi]. simpl in Hi. rewrite map_map in Hi.
    assert (Some_Hu : In (Some (v, w, x)) (map Some u)). { rewrite in_map_iff. eauto. }
    rewrite <- Hi in Some_Hu.
    rewrite in_map_iff in Some_Hu. destruct Some_Hu as [w' [Hw Hw']].
    apply map_nth_error' in Hw. destruct Hw as [[v' x'] [Hvx Hvx']].
    simpl in Hvx. inversion Hvx. subst.
    apply combine_nth_error in Hvx'. simpl in Hvx'. destruct Hvx' as [Hvi Hxi].
    apply map_option_commuting with (f:=(fun w : list A => nth_error w i)) (g:=snd) in Hi.
    - apply rows_spec_5 in Hvi. rewrite Hvi in Hi.
      apply map_Some_eq. assumption.
    - intros w'' vwx Hw''.
      apply map_nth_error with (f:=snd) in Hw''. rewrite map_map in Hw''. simpl in Hw''.
      assert (H : snd = fun vx : (list A) * A => snd vx). { auto. } rewrite <- H in Hw''.
      apply map_nth_error' in Hw''. destruct Hw'' as [y [Hy Hy']].
      apply combine_nth_error in Hy'. destruct Hy' as [_ Hy'].
      rewrite Hy'. rewrite Hy. reflexivity.
  Qed.

  Lemma matrix_by_row_and_column_spec_4 : forall {r : nat} (M : matrix A r) (u : list ((list A) * (list A) * A)),
    In u (columns (matrix_by_row_and_column M)) -> In (map snd u) (columns M).
  Proof.
    intros r M u Hu.
    destruct u as [| [[v w] x] u'].
    - simpl. assert (Hr : r = 0). {
        apply matrix_by_row_and_column'_spec in Hu. auto.
      }
      assert (H : forall v, In v (columns M) -> v = []). {
        intros v Hv. destruct M. simpl in Hv. apply evConstLengthCols in Hv. rewrite Hr in Hv.
        rewrite length_zero_iff_nil in Hv. assumption.
      }
      assert (H' : columns M <> []). {
        rewrite <- length_zero_iff_nil. fold (col_count M).
        rewrite <- matrix_by_row_and_column_spec_0. intros contra. unfold col_count in contra.
        rewrite length_zero_iff_nil in contra. rewrite contra in Hu. inversion Hu.
      }
      destruct (columns M); firstorder.
    - assert (Hw : In w (columns M)). {
         assert (Hvwx : matrix_in (v, w, x) (matrix_by_row_and_column M)). {
           rewrite matrix_in_spec.
           exists ((v, w, x) :: u'). split; [assumption | apply in_eq].
         }
         apply matrix_by_row_and_column_spec_1 in Hvwx.
         destruct Hvwx as [_ [_ [_ H]]]. assumption.
      }
      apply (matrix_by_row_and_column_spec_2 _ _ v w x) in Hu.
      + rewrite <- Hu. assumption.
      + apply in_eq.
  Qed.

  Lemma matrix_by_row_and_column_spec_5 : forall {r : nat} (M : matrix A r) (u : list ((list A) * (list A) * A)),
    In u (rows (matrix_by_row_and_column M)) -> In (map snd u) (rows M).
  Proof.
    intros r M u Hu.
    destruct u as [| [[v w] x] u'].
    - simpl. assert (Hcc : col_count M = 0). {
        rewrite <- matrix_by_row_and_column_spec_0.
        rewrite <- rows_spec_0 with (v:=[]); auto.
      }
      assert (H : forall v, In v (rows M) -> v = []). {
        intros v Hv. apply rows_spec_0 in Hv. rewrite Hcc in Hv. apply length_zero_iff_nil in Hv. assumption.
      }
      assert (H' : rows M <> []). {
        rewrite <- length_zero_iff_nil. intros contra. rewrite rows_spec_1 in contra.
        assert (H'' : rows (matrix_by_row_and_column M) = []). {
          rewrite <- length_zero_iff_nil. rewrite rows_spec_1. assumption.
        }
        rewrite H'' in Hu. inversion Hu.
      }
      destruct (rows M); firstorder.
    - assert (Hv : In v (rows M)). {
         assert (Hvwx : matrix_in (v, w, x) (matrix_by_row_and_column M)). {
           rewrite matrix_in_spec'.
           exists ((v, w, x) :: u'). split; [assumption | apply in_eq].
         }
         apply matrix_by_row_and_column_spec_1 in Hvwx.
         destruct Hvwx as [_ [_ [H _]]]. assumption.
      }
      apply (matrix_by_row_and_column_spec_3 _ _ v w x) in Hu.
      + rewrite <- Hu. assumption.
      + apply in_eq.
  Qed.

  Lemma matrix_by_row_and_column_spec_6 : forall {r : nat} (M : matrix A r),
    map (map snd) (columns (matrix_by_row_and_column M)) = columns M.
  Proof.
    intros r M.
    unfold matrix_by_row_and_column. unfold matrix_by_row_and_column'. simpl.
    rewrite map_map.
    rewrite map_ext_in with (g:=id).
    - apply map_id.
    - intros x Hx. rewrite map_map. simpl. unfold id.
      apply combine_snd.
      apply columns_spec_0 in Hx. rewrite rows_spec_1.
      omega.
  Qed.

  Lemma matrix_by_row_and_column_spec_7 : forall {r : nat} (M : matrix A r) (v w : list A) (x : A) (i j : nat),
    ijth_error (matrix_by_row_and_column M) i j = Some (v, w, x) ->
      In v (rows M) /\
      nth_error (columns M) j = Some w /\
      nth_error v j = Some x.
  Proof.
    intros r M v w x i j H.
    assert (Hin : matrix_in (v, w, x) (matrix_by_row_and_column M)). { apply ijth_error_In in H. assumption. }
    assert (H' := H).
    rewrite ijth_error_transposes in H'.
    unfold ijth_error' in H'.
    destruct (nth_error (rows (matrix_by_row_and_column M)) i) as [u'|] eqn:Hi; [|discriminate].
    unfold ijth_error in H.
    destruct (nth_error (columns (matrix_by_row_and_column M)) j) as [u|] eqn:Hj; [|discriminate].
    assert (Hv : v = map snd u'). {
      apply nth_error_In in H'. apply nth_error_In in Hi.
      apply (matrix_by_row_and_column_spec_3 _ _ _ _ _ H') in Hi.
      assumption.
    }
    assert (Hw : w = map snd u). {
      apply nth_error_In in H. apply nth_error_In in Hj.
      apply (matrix_by_row_and_column_spec_2 _ _ _ _ _ H) in Hj.
      assumption.
    }
    repeat split.
    - apply matrix_by_row_and_column_spec_1 in Hin. destruct Hin as [_ [_ [Hv' _]]].
      assumption.
    - apply nth_error_In in H.
      apply map_nth_error with (f := (map snd)) in Hj.
      rewrite matrix_by_row_and_column_spec_6 in Hj. rewrite <- Hw in Hj. assumption.
    - rewrite Hv.
      assert (Hx : x = snd (v, w, x)). { auto. } rewrite Hx.
      apply map_nth_error. assumption.
  Qed.

  Lemma matrix_by_row_and_column_spec_8 : forall {r : nat} (M : matrix A r) (v w : list A) (x : A),
    matrix_in (v, w, x) (matrix_by_row_and_column M) -> exists (j : nat),
      In v (rows M) /\
      nth_error (columns M) j = Some w /\
      nth_error v j = Some x.
  Proof.
    intros r M v w x H.
    rewrite ijth_error_matrix_in in H. destruct H as [i [j Hij]].
    exists j.
    apply matrix_by_row_and_column_spec_7 in Hij.
    assumption.
  Qed.

  Lemma matrix_filter_by_row_and_column_spec_0 : forall (f : (list A) * (list A) * A -> bool) {r : nat} (M : matrix A r),
    length (filter_columnwise f (matrix_by_row_and_column M)) < r * (col_count M) ->
    exists x v w j,
      In v (rows M) /\
      nth_error (columns M) j = Some w /\
      nth_error v j = Some x /\
      f (v, w, x) = false.
  Proof.
    intros f r M Hf.
    rewrite <- matrix_by_row_and_column_spec_0 in Hf. rewrite  <- flatten_columnwise_length in Hf.
    unfold filter_columnwise in Hf.
    apply list_filter_exhaustive' in Hf.
    destruct Hf as [[[v w] x] [Hxvw Hxvw']].
    rewrite flatten_columnwise_spec_0 in Hxvw.
    apply matrix_by_row_and_column_spec_8 in Hxvw. destruct Hxvw as [j H].
    exists x. exists v. exists w. exists j. firstorder.
  Qed.

End MatrixExtra.
