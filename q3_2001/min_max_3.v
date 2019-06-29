Require Import Omega.

Definition max3 (x y z : nat) := max x (max y z).

Lemma max3_spec_1 : forall x y z,
  (max3 x y z = x /\ y <= x /\ z <= x) \/
  (max3 x y z = y /\ x <= y /\ z <= y) \/
  (max3 x y z = z /\ x <= z /\ y <= z).
Proof.
  intros x y z.
  unfold max3.
  destruct (Nat.max_spec_le y z) as [[Hyz Hyz'] | [Hyz Hyz']]; (try rewrite -> Hyz');
  destruct (Nat.max_spec_le x y) as [[Hxy Hxy'] | [Hxy Hxy']]; (try rewrite -> Hxy');
  destruct (Nat.max_spec_le x z) as [[Hxz Hxz'] | [Hxz Hxz']]; (try rewrite -> Hxz');
  firstorder.
Qed.

Definition min3 (x y z : nat) := min x (min y z).

Lemma min3_spec_0 : forall x y z,
  min3 x y z <= x /\ min3 x y z <= y /\ min3 x y z <= z.
Proof.
  intros x y z.
  unfold min3. repeat split.
  - apply Min.le_min_l.
  - rewrite Min.le_min_r. apply Min.le_min_l.
  - rewrite Min.le_min_r. apply Min.le_min_r.
Qed.

Lemma min3_spec_1 : forall x y z,
  (min3 x y z = x /\ x <= y /\ x <= z) \/
  (min3 x y z = y /\ y <= x /\ y <= z) \/
  (min3 x y z = z /\ z <= x /\ z <= y).
Proof.
  intros x y z.
  unfold min3.
  destruct (Nat.min_spec_le y z) as [[Hyz Hyz'] | [Hyz Hyz']]; (try rewrite -> Hyz');
  destruct (Nat.min_spec_le x y) as [[Hxy Hxy'] | [Hxy Hxy']]; (try rewrite -> Hxy');
  destruct (Nat.min_spec_le x z) as [[Hxz Hxz'] | [Hxz Hxz']]; (try rewrite -> Hxz');
  firstorder.
Qed.

Lemma min3_spec_2 : forall x y z,
  x <> 0 -> y <> 0 -> x + y - min3 x y z <> 0.
Proof.
  intros x y z Hx Hy.
  destruct (min3_spec_1 x y z) as [[H _] | [[H _] | [H [Hz _]]]];
  rewrite -> H; omega.
Qed.
