From Coq Require Import
  Lia Nat ProofIrrelevance VectorDef.
Import PeanoNat.Nat(lt_neq,
                    div_mod,
                    add_0_r,
                    eqb_neq,
                    mod_small,
                    div_small,
                    eqb_eq).
From TinyRAM.Utils Require Import
  Fin Vectors Arith.
Import VectorNotations EqNotations.

Definition b1 := true.
Definition b0 := false.

Definition bitVal : bool -> fin 2.
  intros [|].
  - exists 1; lia.
  - exists 0; lia.
Defined.

Definition Byte := t bool 8.

Definition zeroByte : Byte :=
  const b0 8.

Definition oneByte : Byte :=
  const b1 8.

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

Definition bv_eq {n} (b1 b2 : t bool n) : bool.
  apply (fun x : {b1 = b2} + {b1 <> b2} => if x then true else false).
  apply (VectorEq.eq_dec bool iffb (@iffb_beq)).
Defined.

Definition bv_and {n} (b1 b2 : t bool n) : t bool n :=
  map2 andb b1 b2.

Definition bv_or {n} (b1 b2 : t bool n) : t bool n :=
  map2 orb b1 b2.

Definition bv_xor {n} (b1 b2 : t bool n) : t bool n :=
  map2 xorb b1 b2.

Definition bv_not {n} (b : t bool n) : t bool n :=
  map negb b.

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
  t bool n -> fin (2 ^ n).
  intros n v.
  induction v.
  - exists 0.
    simpl.
    lia.
  - destruct h eqn:hdef.
    + apply (bitvector_fin_double_S IHv).
    + apply (bitvector_fin_double IHv).
Defined.

Definition bitvector_fin_little_fun {n} (v : t bool n) : nat :=
  proj1_sig (bitvector_fin_little v).

Fixpoint fin_bitvector_little_fun (n m : nat) : t bool n :=
  match n with
  | 0 => nil bool
  | S n => 
    cons _ (negb (m mod 2 =? 0)) _ (fin_bitvector_little_fun n (m / 2))
  end.

Definition fin_bitvector_little : forall {n},
  fin (2 ^ n) -> t bool n.
  intros n [f _].
  apply (fin_bitvector_little_fun n f).
Defined.

Theorem bitvector_fin_little_inv_lem_true : forall {n} (f : fin (2 ^ n)),
  fin_bitvector_little (bitvector_fin_double_S f : fin (2 ^ (S n))) =
  cons _ true _ (fin_bitvector_little f).
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
    2: { rewrite PeanoNat.Nat.mod_add. { reflexivity. } { lia. } }
    replace ((1 + f * 2) / 2) with f.
    2: { rewrite PeanoNat.Nat.div_add. { reflexivity. } { lia. } }
    reflexivity.
Qed.

Theorem bitvector_fin_little_inv_lem_false : forall {n} (f : fin (2 ^ n)),
  fin_bitvector_little (bitvector_fin_double f : fin (2 ^ (S n))) =
  cons bool false _ (fin_bitvector_little f).
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
    2: { rewrite PeanoNat.Nat.div_mul. { reflexivity. } { lia. } }
    replace ((f * 2) mod 2) with 0.
    2: { symmetry. rewrite PeanoNat.Nat.mod_mul. { reflexivity. } { lia. } } 
    reflexivity.
Qed.

Theorem bitvector_fin_little_inv : forall {n} (v : t bool n),
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
       with (cons _ (negb (f mod 2 =? 0)) _ (fin_bitvector_little_fun n (f / 2))).
    2: { reflexivity. }
    assert (f = (2 * (f / 2) + f mod 2)) as fsplit.
    { rewrite <- div_mod. { reflexivity. } { lia. } }
    assert (f/2 < 2 ^ n) as fhprp.
    { apply PeanoNat.Nat.div_lt_upper_bound. { lia. } exact fprp. } 
    assert (bitvector_fin_little (fin_bitvector_little (exist _ (f/2) fhprp)) 
            = (exist _ (f/2) fhprp)).
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
  t bool n -> fin (2 ^ n).
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

Definition bitvector_fin_big_fun {n} (v : t bool n) : nat :=
  proj1_sig (bitvector_fin_big v).

Fixpoint fin_bitvector_big_fun (n m : nat) : t bool n :=
  match n with
  | 0 => nil bool
  | S n => 
    cons _ (negb (m / (2 ^ n) =? 0)) _ (fin_bitvector_big_fun n (m mod 2 ^ n))
  end.

Definition fin_bitvector_big : forall {n},
  fin (2 ^ n) -> t bool n.
  intros n [f _].
  apply (fin_bitvector_big_fun n f).
Defined.

Theorem bitvector_fin_big_inv : forall {n} (v : t bool n),
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
        rewrite PeanoNat.Nat.div_str_pos_iff; lia.
      * unfold fin_bitvector_big in IHv.
        rewrite <- IHv.
        f_equal.
        rewrite <- PeanoNat.Nat.add_mod_idemp_r. 2: { assumption. }
        rewrite PeanoNat.Nat.mod_same. 2: { assumption. }
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
      assert (f < 2 ^ n) as fl2n. { rewrite <- PeanoNat.Nat.div_small_iff; lia. }
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
      { apply PeanoNat.Nat.mod_bound_pos; lia. }
      remember (exist (fun r => r < 2 ^ n) (f mod 2 ^ n) fl2n) as f2 eqn:f2Def.
      assert (bitvector_fin_big (fin_bitvector_big f2) = f2).
      { apply IHn. }
      rewrite f2Def in H; unfold fin_bitvector_big in H.
      rewrite H.
      apply subset_eq_compat.
      rewrite (div_mod f (2 ^ n)) at 2. 2: { assumption. }
      rewrite PeanoNat.Nat.add_comm.
      f_equal.
      replace (f / 2 ^ n) with 1. { rewrite PeanoNat.Nat.mul_1_r; reflexivity. }
      symmetry.
      apply div_bet_1. 
      split. 2: { assumption. }
      apply Compare_dec.not_gt; unfold gt.
      intro.
      apply fDiv0.
      rewrite PeanoNat.Nat.div_small_iff; assumption.
Qed.

(* Relating big to little endian *)

Theorem bitvector_fin_big_cons_lem : forall {n},
  S (S (2 * S (2^n) - S (2^n) - 2)) + 2^n - 1 <= 2 ^ (S n).
Proof.
  intro n.
  assert (0 < 2 ^ n).
  { apply zero2pow. }
  simpl; lia.
Qed.

Theorem bitvector_fin_big_cons : forall {n} x (v : t bool n),
  bitvector_fin_big (x :: v) =
  fin_cast bitvector_fin_big_cons_lem
    (fin_add (fin_mul (bitVal x) (fin_max (2^n))) (bitvector_fin_big v)).
Proof.
  intros n x v.
  simpl bitvector_fin_big; unfold fin_cast, fin_max, fin_mul, fin_add.
  destruct (bitvector_fin_big v).
  destruct x eqn:xVal;
  simpl; apply subset_eq_compat; lia.
Qed.

Theorem bitvector_fin_little_snoc_lem : forall {n},
  S (S (2 * S (2^n) - S (2^n) - 2)) + 2^n - 1 <= 2 ^ (n + 1).
Proof.
  intro n.
  assert (0 < 2 ^ n).
  { apply zero2pow. }
  replace (n + 1) with (S n);
  simpl; lia.
Qed.

Theorem bitvector_fin_little_snoc : forall {n} (v : t bool n) x,
  bitvector_fin_little (v ++ [x]) =
  fin_cast bitvector_fin_little_snoc_lem
    (fin_add (fin_mul (bitVal x) (fin_max (2^n))) (bitvector_fin_little v)).
Proof.
  intros n v; induction v.
  - simpl; unfold fin_cast, fin_max, fin_mul, fin_add.
    destruct x; simpl; apply subset_eq_compat; reflexivity.
  - intro x. destruct h; simpl; rewrite IHv;
    destruct (bitvector_fin_little v);
    unfold fin_cast, fin_max, fin_add, fin_mul, bitvector_fin_double_S;
    destruct x; simpl; apply subset_eq_compat; lia.
Qed.

Theorem bitvector_fin_rev : forall {n} (v : t bool n),
  bitvector_fin_big v = bitvector_fin_little (rev v).
Proof.
  intros n v; induction v.
  - rewrite vector_rev_nil_nil; simpl.
    apply subset_eq_compat.
    reflexivity.
  - vector_simp.
    rewrite cast_rew.
    rewrite (rew_f_bubble _ _ (fun m => fin (2 ^ m))).
    rewrite bitvector_fin_little_snoc.
    rewrite <- IHv.
    apply subset_eq_proj1.
    rewrite (rew_f_bubble
                _ (fun x : nat => fin (2 ^ x))
                _ (fun x e => proj1_sig e)).
    rewrite rew_const.
    rewrite bitvector_fin_big_cons.
    destruct (fin_add _ _).
    reflexivity.
Qed.

Theorem fin_bitvector_rev : forall {n} (v : t bool n),
  bitvector_fin_little v = bitvector_fin_big (rev v).
Proof.
  intros n v.
  rewrite bitvector_fin_rev.
  rewrite vector_rev_rev_id.
  reflexivity.
Qed.

Theorem rev_fin_bitvector : forall {n} (f : fin (2 ^ n)),
  fin_bitvector_big f = rev (fin_bitvector_little f).
Proof.
  intros n f.
  rewrite <- fin_bitvector_little_inv at 1.
  rewrite fin_bitvector_rev.
  apply bitvector_fin_big_inv.
Qed.

Theorem rev_bitvector_fin : forall {n} (f : fin (2 ^ n)),
  fin_bitvector_little f = rev (fin_bitvector_big f).
Proof.
  intros n f.
  rewrite <- fin_bitvector_big_inv at 1.
  rewrite bitvector_fin_rev.
  apply bitvector_fin_little_inv.
Qed.

(* Bitvector arithmetic *)

(*least significant bits of addition (unsigned)
  extra leading bit indicates an overflow*)
Definition bv_add {n} (b1 b2 : t bool n) : t bool (S n) :=
  fin_bitvector_big_fun (S n)
    (bitvector_fin_big_fun b1 + bitvector_fin_big_fun b2).

Definition bv_incr {n} (i : nat) (v : t bool n) : t bool n :=
  fin_bitvector_big_fun n ((i + bitvector_fin_big_fun v) mod (2 ^ n)).

(*least significant bits of subtraction (unsigned). 
  extra leading bit indicates a borrow, 0 if borrow, 1 if not.*)
Definition bv_sub {n} (b1 b2 : t bool n) : t bool (S n) :=
  fin_bitvector_big_fun (S n) 
    (bitvector_fin_big_fun b1 + 2 ^ n - bitvector_fin_big_fun b2).

(*Multiplication (unsigned), all bits*)
Definition bv_mul {n} (b1 b2 : t bool n) : t bool (2 * n) :=
  fin_bitvector_big_fun (2 * n) 
    (bitvector_fin_big_fun b1 * bitvector_fin_big_fun b2).

(*least significant bits of multiplication (unsigned)
  additional bits indicate, respecively, an overflow and a result of 0.
  Left vector are MSB, right vector are LSB.*)
Definition bv_mul_flags {n} (b1 b2 : t bool n) : bool * bool * t bool n * t bool n :=
  let prod := (bitvector_fin_big_fun b1 * bitvector_fin_big_fun b2) in
  let (pvH, pvL) := splitat n (fin_bitvector_big_fun (n + n) prod) in
  (2 ^ n <=? prod, prod =? 0, pvH, pvL).

(*Absolute value of signed vector*)
Definition bv_abs {n} (v : t bool (S n)) : t bool (S n) :=
  match v with
  | s :: vs => 
    match s with
    | true => false :: (bv_incr 1 (bv_not vs))
    | false => false :: vs
    end
  end.

(*Negative of signed vector*)
Definition bv_neg {n} (v : t bool (S n)) : t bool (S n) :=
  match v with
  | s :: vs => 
    match s with
    | true => false :: (bv_incr 1 (bv_not vs))
    | false => true :: (bv_incr 1 (bv_not vs))
    end
  end.

(* Computes the upper n bits of the signed multiplication
   of two two's-complement numbers.

  Output is the sign of product (in first bit) followed
  by the upper bits of the absolute-value of the product.

  This means that, for example, -1 * 1 will result in
  10...0, which is not representing a twos complement 
  number.
*)
Definition bv_smulh : forall {n} (b1 b2 : t bool (S n)), 
                                 bool * t bool (S n).
  intros n b1 b2.
  remember (bv_abs b1) as ab1; remember (bv_abs b2) as ab2.
  destruct (bv_mul_flags (tl ab1) (tl ab2)) as [[[ob zb] mresh] _].
  split. { exact ob. }
  destruct zb. { (* if 0 *) exact (const b0 _). }
  exact (xorb (hd b1) (hd b2) :: mresh).
Defined.

(*unsigned division. Extra boolean indicates division by 0.*)
Definition bv_udiv {n} (b1 b2 : t bool n) : bool * t bool n :=
  let den := bitvector_fin_big_fun b2 in
  (den =? 0, fin_bitvector_big_fun n (bitvector_fin_big_fun b1 / den)).

(*unsigned modulus. Extra boolean indicates modulus by 0.*)
Definition bv_umod {n} (b1 b2 : t bool n) : bool * t bool n :=
  let bas := bitvector_fin_big_fun b2 in
  (bas =? 0, fin_bitvector_big_fun n (bitvector_fin_big_fun b1 mod bas)).

(*left-shift by m with zero padding.*)
Definition bv_shl {n} (m : nat) (v : t bool n) : t bool n.
  destruct (m <=? n) eqn:mln.
  - rewrite PeanoNat.Nat.leb_le in mln.
    rewrite <- (PeanoNat.Nat.sub_add m n mln).
    apply (fun x => x ++ const b0 m).
    apply (take _ (PeanoNat.Nat.le_sub_l n m)).
    exact v.
  - exact (const b0 _).
Defined.

(*right-shift by m with zero padding.*)
Definition bv_shr {n} (m : nat) (v : t bool n) : t bool n.
  destruct (m <=? n) eqn:mln.
  - rewrite PeanoNat.Nat.leb_le in mln.
    rewrite <- (Minus.le_plus_minus_r m n mln).
    apply (fun x => const b0 m ++ x).
    apply (fun x => snd (splitat m x)).
    rewrite (Minus.le_plus_minus_r m n mln).
    exact v.
  - exact (const b0 _).
Defined.
