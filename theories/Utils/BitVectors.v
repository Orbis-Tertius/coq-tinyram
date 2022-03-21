From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Fin.
From TinyRAM.Utils Require Import
  Vectors.
From TinyRAM.Utils Require Import
  Arith.
Import PeanoNat.Nat.
Require Import ProofIrrelevance.
Require Import VectorDef.
Import VectorNotations.

Definition Byte := Vector.t bool 8.

Definition zeroByte : Byte :=
  Vector.const false 8.

Definition oneByte : Byte :=
  Vector.const true 8.

Definition iffb (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | false, true => false
  | true, false => false 
  | false, false => true
  end.

Theorem iffb_beq : forall {b1 b2}, (iffb b1 b2 = true) <-> b1 = b2.
  intros [] []; split;
  try reflexivity;
  intro x; discriminate x.
Qed.

Definition bv_eq {n} (b1 b2 : Vector.t bool n) : bool.
  apply (fun x : {b1 = b2} + {b1 <> b2} => if x then true else false).
  apply (VectorEq.eq_dec bool iffb (@iffb_beq)).
Defined.

Definition bv_and {n} (b1 b2 : Vector.t bool n) : Vector.t bool n :=
  Vector.map2 andb b1 b2.

Definition bv_or {n} (b1 b2 : Vector.t bool n) : Vector.t bool n :=
  Vector.map2 orb b1 b2.

Definition bv_xor {n} (b1 b2 : Vector.t bool n) : Vector.t bool n :=
  Vector.map2 xorb b1 b2.

Definition bv_neg {n} (b : Vector.t bool n) : Vector.t bool n :=
  Vector.map negb b.

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

(* Little Endian encoding. *)

Definition bitvector_fin_little : forall {n},
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

Fixpoint fin_bitvector_little_fun (n m : nat) : Vector.t bool n :=
  match n with
  | 0 => Vector.nil bool
  | S n => 
    Vector.cons _ (negb (m mod 2 =? 0)) _ (fin_bitvector_little_fun n (m / 2))
  end.

Definition fin_bitvector_little : forall {n},
  fin (2 ^ n) -> Vector.t bool n.
  intros n [f _].
  apply (fin_bitvector_little_fun n f).
Defined.

Theorem bitvector_fin_little_inv_lem_true : forall {n} (f : fin (2 ^ n)),
  fin_bitvector_little (bitvector_fin_double_S f : fin (2 ^ (S n))) =
  Vector.cons _ true _ (fin_bitvector_little f).
Proof.
  intros n.
  destruct n as [|n]; intros [f fprp].
  - rewrite unique_f0 at 1.
    reflexivity.
  - simpl bitvector_fin_double_S.
    unfold fin_bitvector_little.
    unfold fin_bitvector_little_fun.
    replace (S (f + (f + 0))) with (1 + f * 2).
    2: { lia. }
    replace (((1 + f * 2)) mod 2) with 1.
    2: { rewrite mod_add. { reflexivity. } { lia. } }
    replace ((1 + f * 2) / 2) with f.
    2: { rewrite div_add. { reflexivity. } { lia. } }
    reflexivity.
Qed.

Theorem bitvector_fin_little_inv_lem_false : forall {n} (f : fin (2 ^ n)),
  fin_bitvector_little (bitvector_fin_double f : fin (2 ^ (S n))) =
  Vector.cons bool false _ (fin_bitvector_little f).
Proof.
  intros n.
  destruct n as [|n]; intros [f fprp].
  - rewrite unique_f0 at 1.
    reflexivity.
  - simpl bitvector_fin_double.
    unfold fin_bitvector_little.
    unfold fin_bitvector_little_fun.
    replace (f + (f + 0)) with (f * 2).
    2: { lia. }
    replace (f * 2 / 2) with f.
    2: { rewrite div_mul. { reflexivity. } { lia. } }
    replace ((f * 2) mod 2) with 0.
    2: { symmetry. rewrite mod_mul. { reflexivity. } { lia. } } 
    reflexivity.
Qed.

Theorem bitvector_fin_little_inv : forall {n} (v : Vector.t bool n),
  fin_bitvector_little (bitvector_fin_little v) = v.
Proof.
  intros n v.
  induction v.
  - reflexivity.
  - destruct h; simpl bitvector_fin_little.
    + rewrite bitvector_fin_little_inv_lem_true.
      rewrite IHv.
      reflexivity.
    + rewrite bitvector_fin_little_inv_lem_false.
      rewrite IHv.
      reflexivity.
Qed.

Theorem fin_bitvector_little_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin_little (fin_bitvector_little f) = f.
  intro n.
  induction n as [|n IHn]; intros [f fprp].
  + simpl.
    rewrite unique_f0.
    apply subset_eq_compat.
    reflexivity.
  + unfold fin_bitvector_little.
    replace (fin_bitvector_little_fun (S n) f)
       with (Vector.cons _ (negb (f mod 2 =? 0)) _ (fin_bitvector_little_fun n (f / 2))).
    2: { reflexivity. }
    assert (f = (2 * (f / 2) + f mod 2)) as fsplit.
    { rewrite <- div_mod. { reflexivity. } { lia. } }
    assert (f/2 < 2 ^ n) as fhprp.
    { apply div_lt_upper_bound. { lia. } exact fprp. } 
    assert (bitvector_fin_little (fin_bitvector_little (exist _ (f/2) fhprp)) = (exist _ (f/2) fhprp)).
    { apply IHn. } clear IHn. simpl in H.
    destruct (f mod 2 =? 0) eqn:fmod;
    simpl; rewrite H; clear H; simpl;
    apply subset_eq_compat;
    replace (fst (divmod f 1 0 1)) with (f / 2); try reflexivity.
    - rewrite eqb_eq in fmod.
      rewrite fmod, add_0_r in fsplit.
      lia.
    - replace (f mod 2) with 1 in fsplit.
      { lia. }  
      rewrite eqb_neq in fmod.
      destruct (mod_2_0or1 f). { destruct (fmod H). }
      symmetry; assumption.
Qed.

(* Big Endian encoding. *)

Definition bitvector_fin_big {n} (v : Vector.t bool n) :
  fin (2 ^ n) := bitvector_fin_little (rev v).

Definition fin_bitvector_big {n} (f : fin (2 ^ n)) :
  Vector.t bool n := rev (fin_bitvector_little f).

Theorem bitvector_fin_big_inv : forall {n} (v : Vector.t bool n),
  fin_bitvector_big (bitvector_fin_big v) = v.
Proof.
  intros n v.
  unfold fin_bitvector_big, bitvector_fin_big.
  rewrite bitvector_fin_little_inv.
  apply vector_rev_rev_id.
Qed.

Theorem fin_bitvector_big_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin_big (fin_bitvector_big f) = f.
Proof.
  intros n f.
  unfold fin_bitvector_big, bitvector_fin_big.
  rewrite vector_rev_rev_id.
  apply fin_bitvector_little_inv.
Qed.

Definition bv_add : forall {n} (b1 b2 : Vector.t bool n), Vector.t bool n.
  intros n b1 b2.
  apply fin_bitvector_little; apply bitvector_fin_little in b1, b2.
  destruct b1 as [b1 b1prp]; destruct b2 as [b2 b2prp].
  exists ((b1 + b2) mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.

Definition bv_incr : forall {n}, Vector.t bool n -> nat -> Vector.t bool n.
  intros n b i.
  apply fin_bitvector_little; apply bitvector_fin_little in b.
  destruct b as [b bprp].
  exists ((b + i) mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.

Ltac vector_bubble :=
  match goal with
  | |- context[vector_length_coerce _ (vector_length_coerce _ _)] =>
      rewrite vector_length_coerce_trans
  | |- context[vector_length_coerce _ ?x ++ vector_length_coerce _ ?y] =>
      rewrite (vector_length_coerce_app_funct _ _ x y)
  | |- context[?h :: vector_length_coerce _ ?y] =>
      rewrite (vector_length_coerce_cons_in _ h y)
  | |- context[rev []] =>
      rewrite vector_rev_nil_nil
  | |- context[rev (?h :: ?x)] =>
      rewrite (rev_snoc h x)
  | |- context[rev (?x ++ [?h])] =>
      rewrite (rev_cons h x)
  | |- context[vector_length_coerce _ ?x ++ ?y] =>
      rewrite <- (vector_length_coerce_id (eq_refl (length (to_list y))) y)
  end.

Ltac vector_simp :=
  repeat vector_bubble;
  repeat rewrite vector_length_coerce_id.

Example test : rev [false ; false ; false ; false ; false ]
                 = [ false ; false ; false ; false ; false ].
Proof.
  vector_simp.
  reflexivity.
Qed.
