From Coq Require Import
  Lia.

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

  Definition vector_unappend : forall {A n m},
    Vector.t A (n + m) -> Vector.t A n * Vector.t A m.
  intros A n m v.
  induction n as [|n IHn].
  - split.
    + apply Vector.nil.
    + assumption.
  - simpl in v; destruct (Vector.uncons v) as [vhd vtl].
    destruct (IHn vtl) as [lvtl rv].
    split.
    + apply Vector.cons.
      * apply vhd.
      * apply lvtl.
    + apply rv.
  Defined.

  Theorem vector_append_inv1 : forall {A n m}
    (v : Vector.t A (n + m)),
    uncurry Vector.append (vector_unappend v) = v.
  Admitted.

  Theorem vector_append_inv2 : forall {A n m}
    (v1 : Vector.t A n) (v2 : Vector.t A m),
    vector_unappend (Vector.append v1 v2) = (v1, v2).
  Admitted.

  Definition vector_unconcat : forall {A n m},
    Vector.t A (m * n) -> Vector.t (Vector.t A n) m.
  intros A n m v.
  induction m as [|m IHm].
  - apply Vector.nil.
  - simpl in v; destruct (vector_unappend v) as [vv1 vvtl].
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

  Definition vector_length_coerce : forall {A n m},
    n = m ->
    Vector.t A n ->
    Vector.t A m.
  intros A n m eq v. rewrite <- eq. assumption. Defined.