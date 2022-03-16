From Coq Require Import
  Lia.

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
  destruct eq1.
  rewrite eq_trans_refl_l.
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
    assert (exists (x:A) (vtl:Vector.t A (n + m)), v=Vector.cons A x (n + m) vtl).
    { exists (Vector.hd v). exists (Vector.tl v). apply Vector.eta. }
    destruct H as [x [vtl eq]].
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
  intros A n.
  induction n as [|n IHn];
  intros m.
  - intros v1 v2.
    apply (Vector.case0 (fun v1 => Vector.splitat 0
            (Vector.append v1 v2) = (v1, v2))).
    reflexivity.    
  - intros v1 v2.
    assert (exists (x:A) (vtl:Vector.t A n), v1=Vector.cons A x n vtl).
    { exists (Vector.hd v1). exists (Vector.tl v1). apply Vector.eta. }
    destruct H as [x [vtl eq]].
    rewrite eq.
    assert (Vector.splitat n (Vector.append vtl v2) = (vtl, v2)).
    { apply IHn. }
    simpl.
    destruct (Vector.splitat n (Vector.append vtl v2)) as [vo1 vo2].
    injection H; intros H1 H2.
    rewrite H1, H2.
    reflexivity.
Qed.

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

Theorem vector_concat_inv1 : forall {A n m}
    (v : Vector.t A (n * m)),
    vector_concat (vector_unconcat v) = v.
  Admitted.

Theorem vector_concat_inv2 : forall {A n m}
    (v : Vector.t (Vector.t A n) m),
    vector_unconcat (vector_concat v) = v.
  Admitted.

Definition vector_concat_2 : forall {A n m},
    Vector.t (Vector.t A n) m -> Vector.t A (n * m).
  intros A n m v.
  rewrite PeanoNat.Nat.mul_comm.
  apply vector_concat.
  assumption.
  Defined.