Require Import Omega.

From q3_2001 Require Export min_max_3.
From q3_2001 Require Export ceil.
From q3_2001 Require Export misc.


Section Inequalities.

  Variables (r c m n : nat).
  Variables (Hr : r <> 0) (Hc : c <> 0) (Hm : m <> 0) (Hn : n <> 0).

  Lemma Hmn_spec : {m = 1 /\ n = 1} + {1 < m \/ 1 < n}.
  Proof.
    destruct (Nat.ltb_spec0 1 m) as [Hm' | Hm'];
    destruct (Nat.ltb_spec0 1 n) as [Hn' | Hn'].
    - right. left. assumption.
    - right. left. assumption.
    - right. right. assumption.
    - left. omega.
  Qed.

  Definition k' := ceil (r*c) (c*m + r*n - min3 (c*m) (r*n) (c+r)).

  Lemma k_spec_0 : 1 <= k'.
  Proof.
    destruct (Nat.leb_spec0 1 k') as [Hk|Hk]; [assumption|exfalso].
    assert (Hk' : k' <= 0). { omega. }
    unfold k' in Hk'.
    rewrite ceil_spec_0 in Hk'.
    - rewrite -> Nat.mul_0_r in Hk'. apply Nat.le_0_r in Hk'.
      destruct (mult_is_O _ _ Hk'); contradiction.
    - assert (Hcm : c * m <> 0). { intros contra. apply mult_is_O in contra; omega. }
      assert (Hrn : r * n <> 0). { intros contra. apply mult_is_O in contra; omega. }
      apply (min3_spec_2 (c*m) (r*n) (c+r) Hcm Hrn).
  Qed.

  Lemma k_spec_1 : 1 < m \/ 1 < n -> k' = min3 (ceil r m) (ceil c n) (ceil (r*c) (c*(m-1) + r*(n-1))).
  Proof.
    intros Hmn.
    assert (Hrm : ceil r m = ceil (r*c) (c*m)). {
      rewrite -> ceil_spec_5 with (z:=c); try assumption.
      rewrite (Nat.mul_comm c r). reflexivity.
    }
    assert (Hcn : ceil c n = ceil (r*c) (r*n)). {
      rewrite -> ceil_spec_5 with (z:=r); try assumption; reflexivity.
    }
    rewrite -> Hrm.
    rewrite -> Hcn.
    assert (H : forall x y z, y <> 0 -> z <> 0 -> min (ceil x y) (ceil x z) = ceil x (max y z)). {
      intros x y z Hy Hz.
      destruct (Nat.max_spec_le y z) as [[Hmax Hmax'] | [Hmax Hmax']]; rewrite Hmax';
      destruct (Nat.min_spec_le (ceil x y) (ceil x z)) as [[Hmin Hmin'] | [Hmin Hmin']]; rewrite Hmin'.
      - apply (ceil_spec_4 x y x z Hy (le_refl x)) in Hmax. omega.
      - reflexivity.
      - reflexivity.
      - apply (ceil_spec_4 x z x y Hz (le_refl x)) in Hmax. omega.
    }
    assert (H3 : forall x y z w, y <> 0 -> z <> 0 -> w <> 0 -> min3 (ceil x y) (ceil x z) (ceil x w) = ceil x (max3 y z w)). {
      intros x y z w Hy Hz Hw.
      unfold min3. unfold max3.
      rewrite (H x z w Hz Hw).
      rewrite (H x y (max z w) Hy).
      - reflexivity.
      - destruct (Nat.max_spec_le z w) as [[Hmax Hmax'] | [Hmax Hmax']]; rewrite Hmax'; assumption.
    }
    rewrite H3.
    assert (H' : c * (m - 1) + r * (n - 1) = c*m + r*n - c - r). {
      destruct m as [| m']; destruct n as [| n']; try contradiction.
      simpl. repeat (rewrite <- minus_n_O).
      repeat (rewrite Nat.mul_succ_r).
      rewrite (Nat.add_shuffle0 (c*m') c (r*n' + r)).
      rewrite Nat.add_assoc.
      repeat (rewrite Nat.add_sub).
      reflexivity.
    }
    rewrite H'.
    - unfold k'. apply equal_args.
      destruct (min3_spec_1 (c*m) (r*n) (c+r)) as [[Hmin [Hmin' Hmin'']] | [[Hmin [Hmin' Hmin'']] | [Hmin [Hmin' Hmin'']]]];
      rewrite Hmin;
      destruct (max3_spec_1 (c*m) (r*n) (c * m + r * n - c - r)) as [[Hmax [Hmax' Hmax'']] | [[Hmax [Hmax' Hmax'']] | [Hmax [Hmax' Hmax'']]]];
      rewrite Hmax;
      destruct Hmn as [Hm' | Hn'];
      clear Hrm Hcn H H3 H' Hmin Hmax; omega.
    - intros contra. apply mult_is_O in contra. destruct contra; contradiction.
    - intros contra. apply mult_is_O in contra. destruct contra; contradiction.
    - intros contra. apply plus_is_O in contra. destruct contra as [contra' contra''].
      apply mult_is_O in contra'. apply mult_is_O in contra''.
      omega.
  Qed.

  Lemma min3_cr_spec : forall x y, x + y - min3 x y (x + y) = max x y.
  Proof.
    clear Hm Hn m n.
    intros x y.
    destruct (min3_spec_1 x y (x+y)) as [[Hmin [Hmin' Hmin'']] | [[Hmin [Hmin' Hmin'']] | [Hmin [Hmin' Hmin'']]]];
    destruct (Nat.max_spec x y) as [[Hmax' Hmax] | [Hmax' Hmax]];
    rewrite Hmin; rewrite Hmax; omega.
  Qed.

  Lemma k_spec_2 : k' <= ceil r m.
  Proof.
    destruct Hmn_spec as [[Hm' Hn'] | Hmn].
    - unfold k'. subst.
      repeat (rewrite -> Nat.mul_1_r).
      rewrite min3_cr_spec.
      destruct (Nat.max_spec c r) as [[Hmax' Hmax] | [Hmax' Hmax]]; rewrite Hmax.
      + rewrite <- (Nat.mul_1_r r) at 2.
        rewrite <- ceil_spec_5 with (z:=r); try auto.
        repeat (rewrite ceil_spec_2).
        omega.
      + rewrite <- (Nat.mul_1_r c) at 2.
        rewrite (mult_comm r c).
        rewrite <- ceil_spec_5 with (z:=c); try auto.
    - rewrite k_spec_1. apply min3_spec_0. assumption.
  Qed.

  Lemma k_spec_3 : k' <= ceil c n.
  Proof.
    destruct Hmn_spec as [[Hm' Hn'] | Hmn].
    - unfold k'. subst.
      repeat (rewrite -> Nat.mul_1_r).
      rewrite min3_cr_spec.
      destruct (Nat.max_spec c r) as [[Hmax' Hmax] | [Hmax' Hmax]]; rewrite Hmax.
      + rewrite <- (Nat.mul_1_r r) at 2.
        rewrite <- ceil_spec_5 with (z:=r); try auto.
      + rewrite <- (Nat.mul_1_r c) at 2.
        rewrite (mult_comm r c).
        rewrite <- ceil_spec_5 with (z:=c); try auto.
        repeat (rewrite ceil_spec_2).
        omega.
    - rewrite k_spec_1. apply min3_spec_0. assumption.
  Qed.

  Lemma k_spec_4 : 1 < m \/ 1 < n -> k' <= ceil (r*c) (c*(m-1) + r*(n-1)).
  Proof.
    intros Hmn.
    rewrite k_spec_1. apply min3_spec_0.
    assumption.
  Qed.

  Lemma k_spec_5 : c * ((m-1) * (k'-1)) + r * ((n-1) * (k'-1)) < r*c.
  Proof.
    destruct Hmn_spec as [[Hm' Hn'] | Hmn].
    - subst. simpl. repeat (rewrite -> Nat.mul_0_r). simpl. apply Nat.mul_pos_pos; omega.
    - rewrite -> Nat.mul_assoc. rewrite -> Nat.mul_assoc.
      rewrite <- Nat.mul_add_distr_r.
      rewrite <- ceil_spec_1.
      + pose (H := k_spec_4 Hmn). pose (H' := k_spec_0). omega.
      + unfold not. intros contra. destruct (plus_is_O _ _ contra) as [contra' _].
        rewrite -> contra' in contra. simpl in contra.
        destruct (mult_is_O _ _ contra) as [contra'' | contra''];
        destruct (mult_is_O _ _ contra') as [contra''' | contra'''];
        try contradiction. omega.
  Qed.

End Inequalities.
