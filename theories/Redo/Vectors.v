From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Fin.
Import PeanoNat.Nat.

Definition vector_length_coerce : forall {A n m},
    n = m ->
    Vector.t A n ->
    Vector.t A m.
  intros A n m eq v. rewrite <- eq. assumption. Defined.

Theorem vector_length_coerce_trans : forall {A n m}
    (eq1 : n = m) (eq2 : m = n) (v : Vector.t A n),
    (vector_length_coerce eq2 (vector_length_coerce eq1 v))
    = (vector_length_coerce (eq_trans eq1 eq2) v).
Proof.
  intros A n m eq1 eq2 v.
  destruct eq2.
  reflexivity.
Qed.

Theorem vector_length_coerce_inv : forall {A n m}
    (eq : n = m) (v : Vector.t A n),
    (vector_length_coerce (eq_sym eq) (vector_length_coerce eq v)) = v.
Proof.
  intros A n m eq v.
  destruct eq.
  reflexivity.
Qed.

Theorem vector_length_coerce_inv2 : forall {A n m}
    (eq : m = n) (v : Vector.t A n),
    (vector_length_coerce eq (vector_length_coerce (eq_sym eq) v)) = v.
Proof.
  intros A n m eq v.
  destruct eq.
  reflexivity.
Qed.

Theorem vector_cons_split : forall {A n}
  (v : Vector.t A (S n)), 
  (exists (x:A) (vtl:Vector.t A n), v = Vector.cons A x n vtl).
Proof.
  intros A n v.
  exists (Vector.hd v), (Vector.tl v). apply Vector.eta.
Qed.

Definition bitvector_fin_double_S : forall {n},
  fin n -> fin (2 * n).
  intros n a.
  destruct a as [a afin].
  exists (S (2 * a)).
  lia.
  Defined.

Definition bitvector_fin_double : forall {n},
  fin n -> fin (2 * n).
  intros n a.
  destruct a as [a afin].
  exists (2 * a).
  lia.
  Defined.

Definition bitvector_fin : forall {n},
  Vector.t bool n -> fin (2 ^ n).
  intros n v.
  induction v.
  - exists 0.
    simpl.
    lia.
  - destruct h eqn:hdef.
    + apply (bitvector_fin_double_S IHv).
    + apply (bitvector_fin_double IHv).
Defined.

Definition fin_mod : forall n m,
  n <> 0 -> fin (m * n) -> fin n.
  intros n m meq f.
  destruct f as [f fprp].
  exists (f mod n).
  apply mod_upper_bound.
  assumption.
Defined.

Definition fin_bitvector : forall {n},
  fin (2 ^ n) -> Vector.t bool n.
  intro n.
  induction n as [|n IHn].
  - intro.
    apply Vector.nil.
  - intro f.
    destruct f as [f fpr].
    assert (f = 2 * (f / 2) + f mod 2).
    { apply div_mod. lia. }
    destruct (f mod 2 =? 0) eqn:fmod.
    + rewrite eqb_eq in fmod.
      rewrite fmod, add_0_r in H.
      apply (Vector.cons _ false).
      apply IHn.
      exists (f / 2).
      rewrite (mul_lt_mono_pos_l 2).
      2: { lia. }
      rewrite <- H.
      exact fpr.
    + apply (Vector.cons _ true).
      apply IHn.
      exists (f / 2).
      rewrite (mul_lt_mono_pos_l 2).
      2: { lia. }
      transitivity f.
      2: { exact fpr. }
      rewrite H at 2.
      apply lt_add_pos_r.
      rewrite eqb_neq, neq_0_lt_0 in fmod.
      assumption.
Defined.

Theorem bitvector_fin_inv_lem_true : forall {n} (f : fin (2 ^ n)),
  fin_bitvector (bitvector_fin_double_S f : fin (2 ^ (S n))) =
  Vector.cons bool true _ (fin_bitvector f).
Admitted.


Theorem bitvector_fin_inv_lem_false : forall {n} (f : fin (2 ^ n)),
  fin_bitvector (bitvector_fin_double f : fin (2 ^ (S n))) =
  Vector.cons bool false _ (fin_bitvector f).
Admitted.

Theorem bitvector_fin_inv : forall {n} (v : Vector.t bool n),
  fin_bitvector (bitvector_fin v) = v.
Proof.
  intros n v.
  induction v.
  - reflexivity.
  - destruct h; simpl bitvector_fin.
    + rewrite bitvector_fin_inv_lem_true.
      rewrite IHv.
      reflexivity.
    + rewrite bitvector_fin_inv_lem_false.
      rewrite IHv.
      reflexivity.
Qed.




Theorem fin_bitvector_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin (fin_bitvector f) = f.
  Admitted.

Theorem vector_append_inv1 : forall {A n m}
    (v : Vector.t A (n + m)),
    uncurry Vector.append (Vector.splitat _ v) = v.
Proof.
  intros A n.
  induction n as [|n IHn];
  intros m.
  - intro; reflexivity.
  - intro v.
    simpl in v.
    destruct (vector_cons_split v) as [x [vtl eq]].
    rewrite eq.
    assert (uncurry Vector.append (Vector.splitat n vtl) = vtl).
    { apply IHn. }
    simpl.
    destruct (Vector.splitat n vtl) as [tl1 tl2].
    rewrite <- H.
    reflexivity.
Qed.

Theorem vector_append_inv2 : forall {A n m}
    (v1 : Vector.t A n) (v2 : Vector.t A m),
    Vector.splitat _ (Vector.append v1 v2) = (v1, v2).
  intros A n m v.
  generalize dependent m.
  induction v.
  - reflexivity.
  - simpl.
    intros m vs.
    rewrite IHv.
    reflexivity.
Qed.

Theorem vector_append_split : forall {A n m}
  (v : Vector.t A (n + m)), 
  (exists (vhd : Vector.t A n) (vtl : Vector.t A m),
  v = Vector.append vhd vtl).
Proof.
  intros A n m v.
  rewrite <- (vector_append_inv1 v).
  destruct (Vector.splitat n v) as [v1 v2].
  exists v1, v2.
  reflexivity.
Qed.

Definition vector_concat : forall {A n m},
    Vector.t (Vector.t A n) m -> Vector.t A (m * n).
  intros A n m v.
  induction v.
  - apply Vector.nil.
  - simpl.
    apply Vector.append.
    + apply h.
    + apply IHv.
  Defined.

Definition vector_unconcat : forall {A n m},
    Vector.t A (m * n) -> Vector.t (Vector.t A n) m.
  intros A n m v.
  induction m as [|m IHm].
  - apply Vector.nil.
  - simpl in v; destruct (Vector.splitat _ v) as [vv1 vvtl].
    apply Vector.cons.
    + apply vv1.
    + apply IHm.
      apply vvtl.
  Defined.

Theorem vector_concat_inv1_lem : forall {A n m}
  (v : Vector.t A (n * m))
  (u : Vector.t A m),
  vector_unconcat (Vector.append u v : Vector.t A (S n * m)) =
  Vector.cons _ u _ (vector_unconcat v).
Proof.
  intros A n m v u.
  generalize dependent v.
  induction u.
  - reflexivity.
  - intros v.
    simpl Vector.append.
    simpl vector_unconcat.
    rewrite vector_append_inv2.
    reflexivity.
Qed.

Theorem vector_concat_inv1 : forall {A n m}
  (v : Vector.t A (n * m)),
  vector_concat (vector_unconcat v) = v.
Proof.
  intros A n.
  induction n as [|n IHn];
  intros m v.
  - simpl.
    apply (Vector.case0 (fun v => Vector.nil A = v)).
    reflexivity.
  - simpl in v.
    destruct (vector_append_split v) as [vhd [vtl eq]].
    rewrite eq.
    rewrite vector_concat_inv1_lem.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem vector_concat_inv2 : forall {A n m}
    (v : Vector.t (Vector.t A n) m),
    vector_unconcat (vector_concat v) = v.
  intros A n m.
  induction v.
  - reflexivity.
  - simpl.
    rewrite vector_append_inv2.
    rewrite IHv.
    reflexivity.
Qed.

Definition vector_concat_2 : forall {A n m},
    Vector.t (Vector.t A n) m -> Vector.t A (n * m).
  intros A n m v.
  rewrite PeanoNat.Nat.mul_comm.
  apply vector_concat.
  assumption.
  Defined.
