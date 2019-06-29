Require Import Omega.

From q3_2001 Require Export misc.

Definition ceil (x y : nat) :=
  match y with
  | 0 => x (* Division by zero convention (anything would do). *)
  | S y' => let D := Nat.divmod x y' 0 y' in
              if (snd D) =? y' then fst D else S (fst D)
  end.

Lemma ceil_spec_0 : forall x y z : nat,
  y <> 0 -> (ceil x y <= z <-> x <= y * z).
Proof.
  intros x [|y'] z H; unfold ceil.
  - contradiction.
  - pose (q := (fst (Nat.divmod x y' 0 y'))).
    pose (u := (snd (Nat.divmod x y' 0 y'))).
    fold q. fold u.
    pose (H' := (Nat.divmod_spec x y' 0 y' (le_refl y'))).
    assert (HD : (q, u) = Nat.divmod x y' 0 y'). { symmetry. apply surjective_pairing. }
    rewrite <- HD in H'. destruct H' as [Heq Hu].
    assert (Hq : x = (S y') * q + y' - u). { omega. }
    destruct (u =? y') eqn:H_rem; rewrite -> Hq.
    + apply Nat.eqb_eq in H_rem. rewrite <- H_rem.
      assert (Hrw : forall w, w + u - u = w). { intros w. omega. } rewrite -> (Hrw (S u * q)).
      split; [apply mult_le_compat_l | apply (mult_S_le_reg_l u q z)].
    + apply Nat.eqb_neq in H_rem.
      split; intros H_ineq.
      * assert (H1 : S y' * q + y' - u <= S y' * q + S y'). { omega. }
        assert (H2 : S y' * q + S y' = S y' * S q). { auto. }
        rewrite -> H2 in H1.
        assert (H3 : S y' * S q <= S y' * z). { apply mult_le_compat_l. assumption. }
        omega.
      * assert (H1 : S y' * q + y' - u = S y' * q + (y' - u)). { omega. } rewrite -> H1 in H_ineq.
        assert (H2 : 0 < y' - u). { omega. }
        assert (H3 : S y' * q < S y' * z). { omega. }
        rewrite <- Nat.mul_lt_mono_pos_l in H3.
        -- assumption.
        -- apply Nat.lt_0_succ.
Qed.

Lemma ceil_spec_1 : forall x y z : nat,
  y <> 0 -> (z < ceil x y <-> y * z < x).
Proof.
  intros x y z Hy.
  destruct (Nat.le_gt_cases x (y*z)) as [Hx|Hx];
  destruct (Nat.le_gt_cases (ceil x y) z) as [Hz|Hz]; split; intros H; try omega.
  - rewrite <- (ceil_spec_0 _ _ _ Hy) in Hx. omega.
  - rewrite -> (ceil_spec_0 _ _ _ Hy) in Hz. omega.
Qed.

Lemma ceil_spec_2 : forall x : nat,
  ceil x 1 = x.
Proof.
  intros. assert (H : 1 <> 0). { intros contra. inversion contra. }
  assert (H_lt : ceil x 1 <= x). {
    rewrite -> (ceil_spec_0 _ _ _ H). rewrite Nat.mul_1_l. apply le_refl.
  }
  assert (H_gt : ceil x 1 >= x). {
    unfold ge. rewrite <- (Nat.mul_1_l (ceil x 1)).
    rewrite <- (ceil_spec_0 x 1 (ceil x 1) H). apply le_refl.
  }
  apply Nat.le_antisymm; assumption.
Qed.

Lemma ceil_spec_3 : forall x y : nat,
  y <> 0 -> x <= y * ceil x y.
Proof. intros. rewrite <- ceil_spec_0; trivial. Qed.

Lemma ceil_spec_4 : forall x y x' y' : nat,
  y <> 0 -> x' <= x -> y <= y' -> ceil x' y' <= ceil x y.
Proof.
  intros x y x' y' Hyn0 Hx Hy.
  assert (Hy' : y' <> 0). { omega. }
  rewrite -> (ceil_spec_0 _ _ _ Hy').
  apply (le_trans x' x (y' * ceil x y)).
  - assumption.
  - apply (le_trans x (y * ceil x y) (y' * ceil x y)).
    + apply (ceil_spec_3 _ _ Hyn0).
    + apply mult_le_compat_r. assumption.
Qed.

Lemma ceil_spec_5 : forall x y z : nat,
  y <> 0 -> z <> 0 -> ceil x y = ceil (z*x) (z*y).
Proof.
  intros x y z Hy Hz.
  assert (Hr : ceil (z*x) (z*y) <= ceil x y). {
    apply ceil_spec_0.
    - apply mult_is_O'; assumption.
    - rewrite <- mult_assoc. apply Nat.mul_le_mono_l. apply ceil_spec_3. assumption.
  }
  assert (Hl : ceil x y <= ceil (z*x) (z*y)). {
    apply ceil_spec_0.
    - omega.
    - rewrite -> Nat.mul_le_mono_pos_l with (p:=z).
      + rewrite mult_assoc. apply ceil_spec_3. apply mult_is_O'; assumption.
      + omega.
  }
  apply Nat.le_antisymm; assumption.
Qed.
