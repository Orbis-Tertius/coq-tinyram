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
Import EqNotations.

Definition bitVal : bool -> fin 2.
  intros [|].
  - exists 1; lia.
  - exists 0; lia.
Defined.

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

Definition bv_not {n} (b : Vector.t bool n) : Vector.t bool n :=
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
Proof.
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

Definition bitvector_fin_big : forall {n},
  Vector.t bool n -> fin (2 ^ n).
  intros n v.
  induction v.
  - exists 0.
    simpl.
    lia.
  - destruct h eqn:hdef.
    + assert (fin (S (2 ^ n))) as f2. { apply fin_max. }
      assert (2 ^ n + S (2 ^ n) - 1 <= 2 ^ S n). { simpl; lia. }
      apply (fin_cast H).
      apply fin_add; assumption.
    + assert (2 ^ n <= 2 ^ (S n)). { simpl; lia. }
      apply (fin_cast H).
      assumption.
Defined.

Fixpoint fin_bitvector_big_fun (n m : nat) : Vector.t bool n :=
  match n with
  | 0 => Vector.nil bool
  | S n => 
    Vector.cons _ (negb (m / (2 ^ n) =? 0)) _ (fin_bitvector_big_fun n (m mod 2 ^ n))
  end.

Definition fin_bitvector_big : forall {n},
  fin (2 ^ n) -> Vector.t bool n.
  intros n [f _].
  apply (fin_bitvector_big_fun n f).
Defined.

Theorem zero2pow : forall n, 0 < 2 ^ n.
Proof.
  destruct n. { simpl; lia. }
  change 0 with (0 ^ S n); apply pow_lt_mono_l; lia.
Qed.

Theorem bitvector_fin_big_inv : forall {n} (v : Vector.t bool n),
  fin_bitvector_big (bitvector_fin_big v) = v.
Proof.
  intros n v; induction v.
  - reflexivity.
  - assert (2 ^ n <> 0) as pow0.
    { apply not_eq_sym, lt_neq, zero2pow. }
    destruct h.
    + simpl; unfold fin_cast, fin_max, fin_add.
      destruct (bitvector_fin_big v) as [bfbv bfbvP].
      unfold fin_bitvector_big.
      simpl fin_bitvector_big_fun.
      f_equal.
      * rewrite Bool.negb_true_iff, eqb_neq.
        apply not_eq_sym, lt_neq.
        rewrite div_str_pos_iff; lia.
      * unfold fin_bitvector_big in IHv.
        rewrite <- IHv.
        f_equal.
        rewrite <- add_mod_idemp_r. 2: { assumption. }
        rewrite mod_same. 2: { assumption. }
        rewrite add_0_r.
        rewrite mod_small; trivial. 
    + simpl; unfold fin_cast.
      destruct (bitvector_fin_big v) as [bfbv bfbvP].
      simpl fin_bitvector_big.
      f_equal.
      * rewrite Bool.negb_false_iff, eqb_eq.
        apply div_small; assumption.
      * rewrite mod_small. 2: { assumption. }
        unfold fin_bitvector_big in IHv.
        assumption.
Qed.

Theorem fin_bitvector_big_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin_big (fin_bitvector_big f) = f.
Proof.
  intros n f; induction n; destruct f as [f fP].
  - simpl.
    apply subset_eq_compat.
    simpl in fP.
    lia.
  - assert (2 ^ n <> 0) as pow0.
    { apply not_eq_sym, lt_neq, zero2pow. }
    simpl fin_bitvector_big.
    destruct (f / 2 ^ n =? 0) eqn:fDiv0.
    + rewrite eqb_eq in fDiv0.
      simpl bitvector_fin_big; unfold fin_cast, fin_max, fin_add.
      assert (f < 2 ^ n) as fl2n. { rewrite <- div_small_iff; lia. }
      remember (exist (fun r => r < 2 ^ n) f fl2n) as f2 eqn:f2Def.
      assert (bitvector_fin_big (fin_bitvector_big f2) = f2).
      { apply IHn. }
      rewrite f2Def in H.
      unfold fin_bitvector_big in H.
      rewrite mod_small. 2: { assumption. }
      rewrite H.
      apply subset_eq_compat.
      reflexivity.
    + rewrite eqb_neq in fDiv0.
      simpl bitvector_fin_big; unfold fin_cast, fin_max, fin_add.
      assert ((f mod 2 ^ n) < 2 ^ n) as fl2n.
      { apply mod_bound_pos; lia. }
      remember (exist (fun r => r < 2 ^ n) (f mod 2 ^ n) fl2n) as f2 eqn:f2Def.
      assert (bitvector_fin_big (fin_bitvector_big f2) = f2).
      { apply IHn. }
      rewrite f2Def in H; unfold fin_bitvector_big in H.
      rewrite H.
      apply subset_eq_compat.
      rewrite (div_mod f (2 ^ n)) at 2. 2: { assumption. }
      rewrite add_comm.
      f_equal.
      replace (f / 2 ^ n) with 1. { rewrite mul_1_r; reflexivity. }
      symmetry.
      apply div_bet_1. 
      split. 2: { assumption. }
      apply Compare_dec.not_gt; unfold gt.
      intro.
      apply fDiv0.
      rewrite div_small_iff; assumption.
Qed.

Theorem fin_bitvector_big_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin_big (fin_bitvector_big f) = f.

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

(* Relating big to little endian *)


(* fin vect conversion theorems. *)

Theorem bitvector_fin_little_snoc_lem : forall {n},
  S (S (2 * S (2^n) - S (2^n) - 2)) + 2^n - 1 <= 2 ^ (n + 1).
Proof.
  intro n.
  assert (0 < 2 ^ n).
  { destruct n. { simpl; lia. }
    change 0 with (0 ^ S n); apply pow_lt_mono_l; lia. }
  replace (n + 1) with (S n); simpl; lia.
Qed.

Theorem bitvector_fin_little_snoc : forall {n} x (v : t bool n),
  bitvector_fin_little (v ++ [x]) =
  fin_cast bitvector_fin_little_snoc_lem
    (fin_add (fin_mul (bitVal x) (fin_max (2^n))) (bitvector_fin_little v)).
Proof.
  unfold bitvector_fin_little at 1.

  Search bitvector_fin_little.

Theorem bitvector_fin_big_cons_lem : forall {n},
  S (S (2 * S (2^n) - S (2^n) - 2)) + 2^n - 1 <= 2 ^ (S n).
Proof.
  intro n.
  assert (0 < 2 ^ n).
  { destruct n. { simpl; lia. }
    change 0 with (0 ^ S n); apply pow_lt_mono_l; lia. }
  simpl; lia.
Qed.

Theorem bitvector_fin_big_cons : forall {n} x (v : t bool n),
  bitvector_fin_big (x :: v) =
  fin_cast bitvector_fin_big_cons_lem
    (fin_add (fin_mul (bitVal x) (fin_max (2^n))) (bitvector_fin_big v)).
Proof.
  intros n x v.


(* Bitvector arithmatic *)

Definition bv_carry {n} (b1 b2 : Vector.t bool n) : Vector.t bool (S n).
  replace (S n) with (n + 1).
  - exact (bv_and b1 b2 ++ [false]).
  - lia.
Defined.

Definition bv_addf {n} (b1 b2 : Vector.t bool n) : Vector.t bool (S n) :=
  bv_or (bv_carry b1 b2) (false :: bv_xor b1 b2).

Theorem bv_addf_spec_lem : forall {n},
  (2 ^ n + 2 ^ n - 1) <= 2 ^ (S n).
Proof. intro; simpl; lia. Qed.



Definition bv_addf_spec {n} (b1 b2 : Vector.t bool n) :
  bitvector_fin_big (bv_addf b1 b2) = fin_cast bv_addf_spec_lem
  (fin_add (bitvector_fin_big b1) (bitvector_fin_big b2)).
  apply (rect2 (fun n => fun t1 => fun t2 => 
          bitvector_fin_big (bv_addf t1 t2) = fin_cast bv_addf_spec_lem
          (fin_add (bitvector_fin_big t1) (bitvector_fin_big t2)))).
  - unfold bv_addf, bv_carry.
    rewrite rew_id.
    simpl.
    unfold bitvector_fin_big.
    vector_simp; simpl.
    apply subset_eq_compat.
    reflexivity.
  - intros no v1 v2 IHv1v2 x1 x2.
    apply seq_

    unfold fin_add.
    simpl. Unset Printing Notations.
    Search (eq_rect _ _ ?x _ _ = ?x).
 simpl.




eq_rect_id
 reflexivity. 

  induction b1, b2 using rect2.

(*least significant bits of addition (unsigned)*)
Definition bv_add {n} (b1 b2 : Vector.t bool n) : Vector.t bool n :=
  tl (bv_addf b1 b2).



  intros n b1 b2.
  apply fin_bitvector_big; apply bitvector_fin_big in b1, b2.
  destruct b1 as [b1 b1prp]; destruct b2 as [b2 b2prp].
  exists ((b1 + b2) mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.



Definition bv_incr : forall {n}, nat -> Vector.t bool n -> Vector.t bool n.
  intros n i b.
  apply fin_bitvector_big; apply bitvector_fin_big in b.
  destruct b as [b bprp].
  exists ((i + b) mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.

(*least significant bits of subtraction (unsigned)*)
Definition bv_sub : forall {n} (b1 b2 : Vector.t bool n), Vector.t bool n.
  intros n b1 b2.
  apply fin_bitvector_big; apply bitvector_fin_big in b1, b2.
  destruct b1 as [b1 b1prp]; destruct b2 as [b2 b2prp].
  exists ((b1 + (2 ^ n - b2)) mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.

(*least significant bits of multiplication (unsigned)
  additional bits indicate, respecively, an overflow and a result of 0.*)
Definition bv_mull :
  forall {n} (b1 b2 : Vector.t bool n), 
    bool * bool * Vector.t bool n.
  intros n b1 b2.
  apply bitvector_fin_big in b1, b2.
  destruct b1 as [b1 b1prp]; destruct b2 as [b2 b2prp].
  remember (b1 * b2) as b12.
  split. { exact (2 ^ n <=? b12, b12 =? 0). }
  apply fin_bitvector_big.
  exists (b12 mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.

Definition fin_mul : forall {n m}, fin n -> fin m -> fin (n * m).
  intros n m [fn fnP] [fm fmP].
  exists (fn * fm).
  apply mul_lt_mono_nonneg; lia.
Defined.

(*most significant bits of multiplication (unsigned)*)
(* Note: there's an ambiguity in the spec over whether MSBs are 
   the *actual* MSBs (e.g. "0...01" for 1 * 1) vs the missing
   MSBs half cut off by bv_mull (e.g. "0...0" for 1 * 1).

   I implemented the "second-half" interpretation since
   that's obviously more useful.
*)
Definition bv_umulh : forall {n} (b1 b2 : Vector.t bool n), Vector.t bool n.
  intros n b1 b2.
  apply bitvector_fin_big in b1, b2.
  remember (fin_mul b1 b2) as b12.
  remember (rew (eq_sym (pow_add_r 2 n n)) in b12) as b12'.
  assert (n <= n + n). { lia. }
  apply (take _ H).
  apply fin_bitvector_big.
  exact b12'.
Defined.

(*Absolute value of signed vector*)
Definition bv_abs {n} (v : Vector.t bool (S n)) : Vector.t bool (S n) :=
  match v with
  | s :: vs => 
    match s with
    | true => false :: (bv_incr 1 (bv_not vs))
    | false => false :: vs
    end
  end.

(*Negative of signed vector*)
Definition bv_neg {n} (v : Vector.t bool (S n)) : Vector.t bool (S n) :=
  match v with
  | s :: vs => 
    match s with
    | true => false :: (bv_incr 1 (bv_not vs))
    | false => true :: (bv_incr 1 (bv_not vs))
    end
  end.

(*signed multiplication. Extra boolean indicates an under/overflow.*)
Definition bv_smulh : forall {n} (b1 b2 : Vector.t bool (S n)), 
                                 bool * Vector.t bool (S n).
  intros n b1 b2.
  remember (bv_abs b1) as ab1; remember (bv_abs b2) as ab2.
  destruct (bv_mull (tl ab1) (tl ab2)) as [[ob zb] mres].
  split. { exact ob. }
  destruct zb. { exact (const false _). }
  remember (xorb (hd b1) (hd b2)) as x12.
  destruct x12 eqn:x12Val.
  - exact (bv_neg (false :: mres)).
  - exact (false :: mres).
Defined.

(*unsigned division. Extra boolean indicates division by 0.*)
Definition bv_udiv : forall {n} (b1 b2 : Vector.t bool n), 
                                 bool * Vector.t bool n.
  intros n b1 b2.
  apply bitvector_fin_big in b1, b2.
  destruct b1 as [b1 b1prp]; destruct b2 as [b2 b2prp].
  destruct (b2 =? 0) eqn:b20.
  - split. { exact true. }
    exact (const false _).
  - split. { exact false. }
    rewrite eqb_neq in b20.
    apply fin_bitvector_big.
    exists (b1 / b2).
    apply neq0_div_lt; assumption.
Defined.

(*unsigned modulus. Extra boolean indicates modulus by 0.*)
Definition bv_umod : forall {n} (b1 b2 : Vector.t bool n), 
                                 bool * Vector.t bool n.
  intros n b1 b2.
  apply bitvector_fin_big in b1, b2.
  destruct b1 as [b1 b1prp]; destruct b2 as [b2 b2prp].
  destruct (b2 =? 0) eqn:b20.
  - split. { exact true. }
    exact (const false _).
  - split. { exact false. }
    rewrite eqb_neq in b20.
    apply fin_bitvector_big.
    exists (b1 mod b2).
    transitivity b2.
    + apply mod_upper_bound.
      assumption.
    + assumption.
Defined.
