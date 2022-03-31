From Coq Require Import
  Lia Nat ZArith.Int Numbers.BinNums ProofIrrelevance VectorDef VectorEq BinIntDef.
Import PeanoNat.Nat(add_comm,
                    lt_neq,
                    div_mod,
                    add_0_r,
                    eqb_neq,
                    mod_small,
                    div_small,
                    eqb_eq).
Import BinInt.Z(of_nat, to_nat, opp,
                sub, add, mul, pow,
                leb, le, ltb, lt).
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

Definition bitValN (b : bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.

Definition bitValZ (b : bool) : Z :=
  match b with
  | true => 1
  | false => 0
  end.

Theorem proj1_bitVal : forall {n},
  proj1_sig (bitVal n) = bitValN n.
Proof. intros []; reflexivity. Qed.

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

Definition bv_eq {n} : t bool n -> t bool n -> bool :=
  rect2 (fun _ _ _ => bool)
        true
        (fun _ xs ys r x y => andb (iffb x y) r).

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

Definition bitvector_nat_big {n} (v : t bool n) : nat :=
  proj1_sig (bitvector_fin_big v).

Theorem bitvector_nat_big_lt_2pow {n} (v : t bool n) :
  bitvector_nat_big v < 2 ^ n.
Proof.
  unfold bitvector_nat_big.
  destruct (bitvector_fin_big v) as [f fP].
  assumption.
Qed.

Fixpoint nat_bitvector_big (n m : nat) : t bool n :=
  match n with
  | 0 => nil bool
  | S n => 
    cons _ (negb (m / (2 ^ n) =? 0)) _ (nat_bitvector_big n (m mod 2 ^ n))
  end.

Definition fin_bitvector_big : forall {n},
  fin (2 ^ n) -> t bool n.
  intros n [f _].
  apply (nat_bitvector_big n f).
Defined.

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

Theorem bitvector_nat_big_cons : forall {n} x (v : t bool n),
  bitvector_nat_big (x :: v) =
  proj1_sig (bitVal x) * 2^n + bitvector_nat_big v.
Proof.
  intros n x v.
  unfold bitvector_nat_big at 1.
  rewrite bitvector_fin_big_cons, proj1_fin_cast,
          proj1_fin_add, proj1_fin_mul, proj1_fin_max.
  reflexivity.
Qed.

Theorem bitvector_nat_big_inv : forall {n} (v : t bool n),
  nat_bitvector_big n (bitvector_nat_big v) = v.
Proof.
  intros n v.
  induction v.
  - reflexivity.
  - assert (bitvector_nat_big v < 2 ^ n).
    { apply bitvector_nat_big_lt_2pow. }
    rewrite bitvector_nat_big_cons.
    unfold nat_bitvector_big; fold nat_bitvector_big.
    f_equal.
    + destruct (bitvector_fin_big v); destruct h; simpl proj1_sig.
      * rewrite PeanoNat.Nat.mul_1_l.
        replace (_ / _) with 1. { reflexivity. }
        symmetry; apply div_bet_1; lia.
      * rewrite PeanoNat.Nat.mul_0_l, div_small; simpl; lia.
    + assert (2 ^ n <> 0) as pow0.
      { apply not_eq_sym, lt_neq, zero2pow. }
      replace ((_ * 2 ^ n + _) mod _) with (proj1_sig (bitvector_fin_big v)).
      { apply IHv. }
      rewrite <- PeanoNat.Nat.add_mod_idemp_l.
      2: { assumption. }
      unfold bitvector_nat_big.
      replace ((proj1_sig (bitVal h) * 2 ^ n) mod 2 ^ n)
         with 0.
      destruct (bitvector_fin_big v) as [f fP].
      { simpl; rewrite mod_small; trivial. }
      destruct h.
      * simpl. rewrite add_0_r, PeanoNat.Nat.mod_same; trivial.
      * simpl; rewrite mod_small. { reflexivity. }
        apply zero2pow.
Qed.

Theorem bitvector_fin_big_split : forall {n} (v : t bool n),
    bitvector_fin_big v =
    exist (fun x => x < 2 ^ n)
          (bitvector_nat_big v)
          (bitvector_nat_big_lt_2pow v).
Proof.
  intros n v.
  apply unique_fin; reflexivity.
Qed.

Theorem bitvector_fin_big_inv : forall {n} (v : t bool n),
  fin_bitvector_big (bitvector_fin_big v) = v.
Proof.
  intros n v.
  rewrite bitvector_fin_big_split.
  simpl; rewrite bitvector_nat_big_inv.
  reflexivity.
Qed.

Theorem nat_bitvector_big_inv : forall n f,
  f < 2 ^ n ->
  bitvector_nat_big (nat_bitvector_big n f) = f.
Proof.
  intros n; induction n; intros f fP. 
  - unfold bitvector_nat_big.
    simpl; simpl in fP; lia.
  - assert (2 ^ n <> 0) as pow0.
    { apply not_eq_sym, lt_neq, zero2pow. }
    assert ((f mod 2 ^ n) < 2 ^ n) as fl2n.
    { apply PeanoNat.Nat.mod_bound_pos; lia. }
    simpl nat_bitvector_big.
    destruct (f / 2 ^ n =? 0) eqn:fDiv0;
    unfold bitvector_nat_big;
    simpl bitvector_fin_big; unfold fin_cast, fin_max, fin_add;
    rewrite bitvector_fin_big_split; simpl;
    rewrite (IHn (f mod 2 ^ n) fl2n).
    + rewrite eqb_eq in fDiv0.
      rewrite mod_small. { reflexivity. }
      rewrite <- PeanoNat.Nat.div_small_iff; assumption.
    + rewrite eqb_neq in fDiv0.
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

Theorem fin_bitvector_big_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin_big (fin_bitvector_big f) = f.
Proof.
  intros n [f fP].
  unfold fin_bitvector_big; rewrite bitvector_fin_big_split.
  apply subset_eq_compat.
  rewrite (nat_bitvector_big_inv n f); trivial.
Qed.

(* Relating big to little endian *)

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

(* Misc. Theorems *)

Theorem bitvector_nat_big_app : 
  forall {n m} (v1 : t bool n) (v2 : t bool m), 
  bitvector_nat_big (v1 ++ v2) =
  bitvector_nat_big v1 * 2 ^ m + bitvector_nat_big v2.
Proof.
  intros n m v1 v2; induction v1.
  - reflexivity.
  - simpl; repeat rewrite bitvector_nat_big_cons.
    rewrite IHv1, PeanoNat.Nat.pow_add_r.
    lia.
Qed.

Theorem bitvector_fin_big_0_0 : forall {n} (v : t bool n),
  bv_eq v (Vector.const b0 n) =
  (bitvector_nat_big v =? 0).
Proof.
  induction v.
  - reflexivity.
  - rewrite bitvector_nat_big_cons; simpl.
    destruct h; simpl. 2: { apply IHv. }
    symmetry; rewrite eqb_neq.
    assert (0 < 2 ^ n). { apply zero2pow. } 
    lia.
Qed.

Theorem bv_eq_equiv : forall {n} (v1 v2 : t bool n),
  (bv_eq v1 v2 = true) <-> v1 = v2.
Proof.
  apply rect2.
  - split; reflexivity.
  - intros n v1 v2 IHv; split.
    + simpl; intro H; apply andb_prop in H; destruct H.
      rewrite iffb_beq in H; f_equal; auto.
      rewrite <- IHv; assumption.
    + intro H; injection H; intros veq eab.
      apply inj_pair2 in veq.
      simpl bv_eq; rewrite Bool.andb_true_iff; split.
      * rewrite iffb_beq; assumption.
      * rewrite IHv; assumption.
Qed.

Theorem bitvector_fin_big_0_const :
  forall {n} (v : t bool n),
    (v = (Vector.const b0 n)) <-> (bitvector_nat_big v = 0).
Proof.
  intros n v.
  rewrite <- bv_eq_equiv, <- eqb_eq, <- Bool.eq_iff_eq_true.
  apply bitvector_fin_big_0_0.
Qed.

(* Bitvector arithmetic *)

(*least significant bits of addition (unsigned)
  extra leading bit indicates an overflow*)
Definition bv_add {n} (b1 b2 : t bool n) : t bool (S n) :=
  nat_bitvector_big (S n)
    (bitvector_nat_big b1 + bitvector_nat_big b2).

Theorem bv_add_correct_1 : forall {n} (b1 b2 : t bool n),
  bv_add b1 b2 = nat_bitvector_big (S n)
    (bitvector_nat_big b1 + bitvector_nat_big b2).
Proof. reflexivity. Qed.

Theorem bv_add_correct_2 : forall {n} (n1 n2 : nat),
  n1 < 2 ^ n -> n2 < 2 ^ n ->
  n1 + n2 = bitvector_nat_big (
  bv_add (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof.
  intros.
  rewrite bv_add_correct_1.
  repeat rewrite nat_bitvector_big_inv; try lia.
  simpl; lia.
Qed.

Definition bv_incr {n} (i : nat) (v : t bool n) : t bool n :=
  nat_bitvector_big n ((i + bitvector_nat_big v) mod (2 ^ n)).

(*least significant bits of subtraction (unsigned). 
  extra leading bit indicates a borrow, 0 if borrow, 1 if not.*)
Definition bv_sub {n} (b1 b2 : t bool n) : t bool (S n) :=
  nat_bitvector_big (S n) 
    (bitvector_nat_big b1 + 2 ^ n - bitvector_nat_big b2).

Theorem bv_sub_correct_1 : forall {n} (b1 b2 : t bool n),
  bv_sub b1 b2 = nat_bitvector_big (S n) 
    (bitvector_nat_big b1 + 2 ^ n - bitvector_nat_big b2).
Proof. reflexivity. Qed.

Theorem bv_sub_correct_2 : forall {n} (n1 n2 : nat),
  n1 < 2 ^ n -> n2 < 2 ^ n ->
  n1 + 2 ^ n - n2 = bitvector_nat_big (
  bv_sub (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof. 
  intros.
  rewrite bv_sub_correct_1.
  repeat rewrite nat_bitvector_big_inv; try lia.
  simpl; lia.
Qed.

(*least significant bits of multiplication (unsigned)
  additional bits indicate, respecively, an overflow and a result of 0.
  Left vector are MSB, right vector are LSB.*)
Definition bv_mul_flags {n} (b1 b2 : t bool n) : bool * bool * t bool n * t bool n :=
  let prod := (bitvector_nat_big b1 * bitvector_nat_big b2) in
  let (pvH, pvL) := splitat n (nat_bitvector_big (n + n) prod) in
  (2 ^ n <=? prod, prod =? 0, pvH, pvL).

(*Multiplication (unsigned), all bits*)
Definition bv_mul {n} (b1 b2 : t bool n) : t bool (n + n) :=
  (fun x => snd (fst x) ++ snd x) (bv_mul_flags b1 b2).

Theorem bv_mul_correct_1 : forall {n} (b1 b2 : t bool n),
  bv_mul b1 b2 = nat_bitvector_big (n + n) 
    (bitvector_nat_big b1 * bitvector_nat_big b2).
Proof.
  intros n b2 b3.
  unfold bv_mul, bv_mul_flags.
  destruct (splitat n _) eqn:splitEq; simpl.
  apply VectorSpec.append_splitat in splitEq.
  symmetry; assumption.
Qed.

Theorem bv_mul_correct_2 : forall {n} (n1 n2 : nat),
  n1 < 2 ^ n -> n2 < 2 ^ n ->
  n1 * n2 = bitvector_nat_big (
  bv_mul (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof. 
  intros.
  rewrite bv_mul_correct_1.
  repeat rewrite nat_bitvector_big_inv; try lia.
  rewrite PeanoNat.Nat.pow_add_r.
  apply PeanoNat.Nat.mul_lt_mono; lia.
Qed.

Theorem lt_mul_cap : 
  forall a b c, 0 < c -> a + b * c < c -> b = 0.
Proof.
  intros.
  assert (b * c < 1 * c) as bclt. { lia. }
  rewrite <- PeanoNat.Nat.mul_lt_mono_pos_r in bclt; lia.
Qed.

Theorem bv_mull_high_const0 : forall {n} (b1 b2 : t bool n),
  (bitvector_nat_big b1 * bitvector_nat_big b2 < 2 ^ n)
  <-> (fst (splitat n (bv_mul b1 b2)) = const b0 _).
Proof.
  intros n b1 b2.
  rewrite <- nat_bitvector_big_inv at 1.
  2: { rewrite PeanoNat.Nat.pow_add_r.
       apply PeanoNat.Nat.mul_lt_mono;
       apply bitvector_nat_big_lt_2pow. }
  rewrite <- bv_mul_correct_1.
  destruct (splitat _ _) as [b12h b12l] eqn:sE; simpl fst.
  apply Vector.append_splitat in sE; rewrite sE.
  rewrite bitvector_nat_big_app.
  split.
  - intro; rewrite bitvector_fin_big_0_const.
    rewrite add_comm in H. apply lt_mul_cap in H; lia.
  - intro H; rewrite bitvector_fin_big_0_const in H.
    rewrite H; simpl.
    apply bitvector_nat_big_lt_2pow.
Qed.

(*unsigned division. Extra boolean indicates division by 0.*)
Definition bv_udiv_flag {n} (b1 b2 : t bool n) : bool * t bool n :=
  let den := bitvector_nat_big b2 in
  (den =? 0, nat_bitvector_big n (bitvector_nat_big b1 / den)).

Definition bv_udiv {n} (b1 b2 : t bool n) : t bool n :=
  snd (bv_udiv_flag b1 b2).

Theorem bv_udiv_correct_1 : forall {n} (b1 b2 : t bool n),
  bv_udiv b1 b2 = nat_bitvector_big n 
    (bitvector_nat_big b1 / bitvector_nat_big b2).
Proof.
  intros n b2 b3.
  unfold bv_udiv, bv_udiv_flag.
  reflexivity.
Qed.

Theorem bv_udiv_correct_2 : forall {n} (n1 n2 : nat),
  n1 < 2 ^ n -> n2 < 2 ^ n -> n2 <> 0 ->
  n1 / n2 = bitvector_nat_big (
  bv_udiv (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof. 
  intros.
  rewrite bv_udiv_correct_1.
  repeat rewrite nat_bitvector_big_inv; try lia.
  apply neq0_div_lt; assumption.
Qed.

(*unsigned modulus. Extra boolean indicates modulus by 0.*)
Definition bv_umod_flag {n} (b1 b2 : t bool n) : bool * t bool n :=
  let bas := bitvector_nat_big b2 in
  (bas =? 0, nat_bitvector_big n (bitvector_nat_big b1 mod bas)).

Definition bv_umod {n} (b1 b2 : t bool n) : t bool n :=
  snd (bv_umod_flag b1 b2).

Theorem bv_umod_correct_1 : forall {n} (b1 b2 : t bool n),
  bv_umod b1 b2 = nat_bitvector_big n 
    (bitvector_nat_big b1 mod bitvector_nat_big b2).
Proof.
  intros n b2 b3.
  unfold bv_umod, bv_umod_flag.
  reflexivity.
Qed.

Theorem bv_umod_correct_2 : forall {n} (n1 n2 : nat),
  n1 < 2 ^ n -> n2 < 2 ^ n -> n2 <> 0 ->
  n1 mod n2 = bitvector_nat_big (
  bv_umod (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof. 
  intros.
  rewrite bv_umod_correct_1.
  repeat rewrite nat_bitvector_big_inv; try lia.
  rewrite PeanoNat.Nat.mod_eq; try lia.
Qed.

(*left-shift by m with zero padding.*)
Definition bv_shl {n} (m : nat) (v : t bool n) : t bool n.
  destruct (m <=? n) eqn:mln.
  - rewrite PeanoNat.Nat.leb_le in mln.
    rewrite <- (PeanoNat.Nat.sub_add m n mln).
    apply (fun x => x ++ const b0 m).
    apply (fun x => snd (splitat m x)).
    rewrite (Minus.le_plus_minus_r m n mln).
    exact v.
  - exact (const b0 _).
Defined.

Theorem bv_shl_correct : forall {n} m (v : t bool (m + n)),
  bv_shl m v = cast (snd (splitat m v) ++ const b0 m) (add_comm n m).
Proof.
  intros n m v.
  unfold bv_shl.
  assert (m <=? m + n = true).
  { rewrite PeanoNat.Nat.leb_le. lia. }
  rewrite (dep_if_true _ _ _ _ H).
  destruct (splitat m v) as [v1 v2] eqn:spvE.
  apply VectorSpec.append_splitat in spvE; rewrite spvE.
  unfold eq_rec_r, eq_rec; repeat rewrite <- cast_rew.
  rewrite cast_app_l, Vector.splitat_append.
  simpl; vector_simp.
  f_equal; apply proof_irrelevance.
Qed.

(*right-shift by m with zero padding.*)
Definition bv_shr {n} (m : nat) (v : t bool n) : t bool n.
  destruct (m <=? n) eqn:mln.
  - rewrite PeanoNat.Nat.leb_le in mln.
    rewrite <- (Minus.le_plus_minus_r m n mln).
    apply append.
    + exact (const b0 m).
    + rewrite <- (Minus.le_plus_minus_r m n mln), add_comm in v.
      apply (splitat (n - m) v).
  - exact (const b0 _).
Defined.

Theorem bv_shr_correct : forall {n} m (v : t bool (n + m)),
  bv_shr m v = cast (const b0 m ++ fst (splitat n v)) (add_comm m n).
Proof.
  intros n m v.
  unfold bv_shr.
  assert (m <=? n + m = true).
  { rewrite PeanoNat.Nat.leb_le. lia. }
  rewrite (dep_if_true _ _ _ _ H).
  destruct (splitat n v) as [v1 v2] eqn:spvE.
  apply VectorSpec.append_splitat in spvE; rewrite spvE.
  unfold eq_rec_r, eq_rec; repeat rewrite <- cast_rew.
  vector_simp; rewrite cast_app_r. 
  rewrite Vector.splitat_append.
  simpl; vector_simp.
  f_equal; apply proof_irrelevance.
Qed.

(* two's complement signed integer representation. *)

Fixpoint twos_complement' {n} (v : t bool n) : nat :=
  match v with
  | [] => 0
  | x :: xs => bitValN x * (2 ^ (n - 1)) + twos_complement' xs
  end.

Definition twos_complement {n} (v : t bool (S n)) : Z :=
  match v with
  | x :: xs => sub (of_nat (twos_complement' xs))
                   (of_nat (bitValN x * (2 ^ n)))
  end.

Theorem twos_complement_big : forall {n} (v : t bool n),
  twos_complement' v = bitvector_nat_big v.
Proof.
  intros n v; induction v.
  - reflexivity.
  - simpl twos_complement'.
    unfold bitvector_nat_big.
    rewrite bitvector_fin_big_cons.
    rewrite proj1_fin_cast, proj1_fin_add, proj1_fin_mul,
            proj1_fin_max, proj1_bitVal.
    f_equal.
    + rewrite PeanoNat.Nat.sub_0_r; reflexivity.
    + exact IHv.
Qed.

Theorem twos_complement_min : forall {n} (v : t bool (S n)),
  le (opp (pow 2 (of_nat n))) (twos_complement v).
Proof.
  intros n v.
  rewrite <- BinInt.Z.sub_0_l.
  rewrite (Vector.eta v).
  simpl twos_complement.
  apply BinInt.Z.sub_le_mono. { apply Zorder.Zle_0_nat. }
  destruct (hd v).
  2: { simpl bitValN; rewrite PeanoNat.Nat.mul_0_l.
       apply BinInt.Z.pow_nonneg; lia. }
  simpl bitValN; rewrite PeanoNat.Nat.mul_1_l.
  change (Zpos (xO xH)) with (of_nat 2).
  rewrite Z_inj_pow.
  apply Znat.inj_le.
  destruct n; apply le_n.
Qed.

Theorem twos_complement_max : forall {n} (v : t bool (S n)),
  lt (twos_complement v) (pow 2 (of_nat n)).
Proof.
  intros n v.
  rewrite (Vector.eta v).
  simpl twos_complement.
  rewrite (BinInt.Zminus_0_l_reverse (pow _ _)).
  apply BinInt.Z.sub_lt_le_mono. 2: { apply Zorder.Zle_0_nat. }
  change (Zpos (xO xH)) with (of_nat 2).
  rewrite Z_inj_pow.
  apply Znat.inj_lt.
  rewrite twos_complement_big.
  apply bitvector_nat_big_lt_2pow.
Qed.

Definition twos_complement_inv (n : nat) (z : Z) : t bool (S n) :=
  match ltb z 0 with
  | true => nat_bitvector_big _ (Z.to_nat (add z (pow 2 (of_nat (S n)))))
  | false => nat_bitvector_big _ (Z.to_nat z)
  end.

Theorem twos_complement_iso_1 : forall {n} (v : t bool (S n)),
  twos_complement_inv n (twos_complement v) = v.
Proof.
  intros n v.
  assert (twos_complement' (tl v) < 2 ^ n).
  { rewrite twos_complement_big; apply bitvector_nat_big_lt_2pow. }
  rewrite (Vector.eta v).
  simpl.
  destruct (hd v); simpl bitValN.
  - rewrite PeanoNat.Nat.mul_1_l, <- opp_sub_swap, <- Znat.Nat2Z.inj_sub.
    2: { apply PeanoNat.Nat.lt_le_incl; assumption. }
    unfold twos_complement_inv.
    replace (ltb _ 0) with true.
    2: { symmetry; rewrite Z_ltb_lt, BinInt.Z.opp_neg_pos.
         change Z0 with (of_nat 0). apply Znat.inj_lt; lia. }
    rewrite Znat.Nat2Z.inj_sub. 2: { lia. }
    rewrite opp_sub_swap.
    rewrite <- BinInt.Z.sub_sub_distr, <- (opp_sub_swap (pow _ _) _).
    change (Zpos _) with (of_nat 2).
    rewrite Z_inj_pow, <- Znat.Nat2Z.inj_sub. 2: { simpl; lia. }
    replace (2 ^ S n - 2 ^ n) with (2 ^ n). 2: { simpl; lia. }
    rewrite BinInt.Z.sub_opp_r, <- Znat.Nat2Z.inj_add.
    rewrite Znat.Nat2Z.id.
    unfold nat_bitvector_big; f_equal.
    + replace (_ / _) with 1. { reflexivity. }
      symmetry; apply div_bet_1; lia.
    + fold nat_bitvector_big.
      assert (2 ^ n <> 0).
      { apply PeanoNat.Nat.pow_nonzero; lia. }
      rewrite <- PeanoNat.Nat.add_mod_idemp_r. 2: { assumption. }
      rewrite PeanoNat.Nat.mod_same. 2: { assumption. }
      rewrite add_0_r, mod_small. 2: { assumption. }
      rewrite twos_complement_big. 
      apply bitvector_nat_big_inv.
  - simpl of_nat; rewrite BinInt.Z.sub_0_r.
    unfold twos_complement_inv.
    replace (ltb (of_nat (twos_complement' (tl v))) 0)
       with false.
    2: { symmetry; rewrite Z_nltb_ge. apply Znat.Nat2Z.is_nonneg. }
    rewrite Znat.Nat2Z.id.
    unfold nat_bitvector_big; fold nat_bitvector_big.
    f_equal.
    + replace (_ / _) with 0. { reflexivity. }
      symmetry; apply div_small; assumption.
    + replace (_ mod _) with (twos_complement' (tl v)).
      2: { symmetry; apply mod_small; assumption. }
      rewrite twos_complement_big.
      apply bitvector_nat_big_inv.
Qed.

Theorem twos_complement_iso_2 : forall n z,
  le (opp (pow 2 (of_nat n))) z -> 
  lt z (pow 2 (of_nat n)) ->
  twos_complement (twos_complement_inv n z) = z.
Proof.
  intros n z lez ltz.
  assert (2 ^ n <> 0).
  { apply PeanoNat.Nat.pow_nonzero; lia. }
  unfold twos_complement_inv.
  destruct (ltb z 0) eqn:ltz0.
  - rewrite Z_ltb_lt in ltz0.
    assert (0 < to_nat (opp z)). { lia. }
    rewrite BinInt.Z.add_comm, <- BinInt.Z.sub_opp_r.
    rewrite Znat.Z2Nat.inj_sub. 2: { lia. }
    rewrite Z2_inj_pow; try lia.
    change (to_nat _) with 2 at 1.
    rewrite Znat.Nat2Z.id.
    unfold nat_bitvector_big, twos_complement;
    fold nat_bitvector_big.
    assert ((to_nat (opp z)) <= 2 ^ n).
    { rewrite <- Znat.Nat2Z.id, <- Znat.Z2Nat.inj_le; try lia;
      rewrite opp_le_swap_l, <- Z_inj_pow; exact lez. }
    replace (_ / _) with 1.
    2: { symmetry; apply div_bet_1; simpl; lia. }
    replace (_ mod _) with (2 ^ n - to_nat (opp z)).
    2: { replace (2 ^ S n - _) with (2 ^ n + (2 ^ n - to_nat (opp z))).
         rewrite <- PeanoNat.Nat.add_mod_idemp_l, PeanoNat.Nat.mod_same.
         simpl. symmetry; apply mod_small; lia. assumption. assumption.
         simpl; lia. }
    simpl; rewrite twos_complement_big, nat_bitvector_big_inv; lia.
  - rewrite Z_nltb_ge in ltz0.
    assert (0 <= to_nat z). { lia. }
    assert (to_nat z < 2 ^ n).
    { rewrite Znat.Z2Nat.inj_lt, Z2_inj_pow, Znat.Nat2Z.id in ltz; try lia.
      assumption. }
    unfold nat_bitvector_big; fold nat_bitvector_big.
    rewrite mod_small, div_small; try assumption.
    simpl; rewrite twos_complement_big, nat_bitvector_big_inv; lia.
Qed.

Theorem twos_complement_sign : forall n z,
  le (opp (pow 2 (of_nat n))) z -> 
  lt z (pow 2 (of_nat n)) ->
  hd (twos_complement_inv n z) = ltb z Z0.
Proof.
  intros n z zmin zmax.
  unfold twos_complement_inv.
  destruct (ltb z 0) eqn:ltz0; unfold nat_bitvector_big.
  - rewrite Z_ltb_lt in ltz0.
    replace (_ / _) with 1. { reflexivity. }
    rewrite BinInt.Z.add_comm, <- BinInt.Z.sub_opp_r.
    rewrite Znat.Z2Nat.inj_sub. 2: { lia. }
    rewrite Z2_inj_pow; try lia.
    change (to_nat _) with 2 at 1.
    rewrite Znat.Nat2Z.id.
    assert ((to_nat (opp z)) <= 2 ^ n).
    { rewrite <- Znat.Nat2Z.id, <- Znat.Z2Nat.inj_le; try lia;
      rewrite opp_le_swap_l, <- Z_inj_pow; lia. }
    symmetry; apply div_bet_1; simpl; lia.
  - rewrite Z_nltb_ge in ltz0.
    replace (_ / _) with 0. { reflexivity. }
    assert (to_nat z < 2 ^ n).
    { rewrite Znat.Z2Nat.inj_lt, Z2_inj_pow, Znat.Nat2Z.id in zmax; try lia.
      assumption. }
    rewrite div_small; lia.
Qed.

(* signed bitvector arithmetic *)

(*Absolute value of signed vector*)
Definition bv_abs {n} (v : t bool (S n)) : t bool n :=
  nat_bitvector_big n (Z.abs_nat (twos_complement v)).
(*
Definition bv_abs {n} (v : t bool (S n)) : t bool n :=
  match v with
  | s :: vs => 
    match s with
    | true => bv_incr 1 (bv_not vs)
    | false => vs
    end
  end.
*)

Theorem bv_abs_correct : forall {n} (v : t bool (S n)),
  bv_abs v = nat_bitvector_big n (Z.abs_nat (twos_complement v)).
Proof. reflexivity. Qed.

(*Negative of signed vector*)
Definition bv_neg {n} (v : t bool (S n)) : t bool (S n) :=
  twos_complement_inv n (opp (twos_complement v)).
(*
Definition bv_neg {n} (v : t bool (S n)) : t bool (S n) :=
  match v with
  | s :: vs => 
    match s with
    | true => false :: (bv_incr 1 (bv_not vs))
    | false => true :: (bv_incr 1 (bv_not vs))
    end
  end.
*)

Theorem bv_neg_correct_1 : forall {n} (v : t bool (S n)),
  bv_neg v = twos_complement_inv n (opp (twos_complement v)).
Proof. reflexivity. Qed.

Theorem bv_neg_correct_2 : forall {n} (z : Z),
  lt (opp (pow 2 (of_nat n))) z ->
  lt z (pow 2 (of_nat n)) ->
  opp z = twos_complement (bv_neg (twos_complement_inv n z)).
Proof.
  intros; rewrite bv_neg_correct_1.
  repeat rewrite twos_complement_iso_2; try lia.
Qed.

(* signed multiplication *)
Definition bv_smul {n} (b1 b2 : t bool (S n)) : t bool (S (n + n)) :=
  twos_complement_inv (n + n) 
    (mul (twos_complement b1) (twos_complement b2)).

Theorem bv_smul_correct_1 : forall {n} (b1 b2 : t bool (S n)),
  bv_smul b1 b2 = twos_complement_inv (n + n) 
    (mul (twos_complement b1) (twos_complement b2)).
Proof. reflexivity. Qed.

Theorem bv_smul_correct_2 : forall {n} (z1 z2 : Z),
  lt (opp (pow 2 (of_nat n))) z1 -> lt z1 (pow 2 (of_nat n)) ->
  lt (opp (pow 2 (of_nat n))) z2 -> lt z2 (pow 2 (of_nat n)) ->
  mul z1 z2 = twos_complement 
    (bv_smul (twos_complement_inv n z1) (twos_complement_inv n z2)).
Proof. 
  intros. rewrite bv_smul_correct_1.
  repeat rewrite twos_complement_iso_2; try lia;
  rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
  - apply le_opp_mul_mul; lia.
  - apply lt_mul_mul; lia.
Qed.

Theorem bv_smul_correct_sign : forall {n} (b1 b2 : t bool (S n)),
  (lt (opp (pow 2 (of_nat n))) (twos_complement b1)) ->
  (lt (opp (pow 2 (of_nat n))) (twos_complement b2))->
  hd (bv_smul b1 b2) = ltb (mul (twos_complement b1) (twos_complement b2)) 0.
Proof.
  intros n b1 b2.
  rewrite bv_smul_correct_1.
  intros min1 min2.
  remember (mul _ _) as m.
  unfold twos_complement_inv.
  destruct (ltb _ _) eqn:ltm.
  - change 2%Z with (of_nat 2).
    unfold nat_bitvector_big; change (hd (?x :: _)) with x.
    rewrite Z_inj_pow, <- (BinInt.Z.opp_involutive m), BinInt.Z.add_opp_l,
            Znat.Z2Nat.inj_sub, Znat.Nat2Z.id; try lia.
    replace (_ / _) with 1. { reflexivity. }
    assert (to_nat (opp m) <= 2 ^ (n + n)).
    { rewrite <- Znat.Nat2Z.id, <- Znat.Z2Nat.inj_le; try lia.
      rewrite <- Z_inj_pow, Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      rewrite <- BinInt.Z.pow_add_r, Heqm, opp_le_swap_l, BinInt.Z.pow_add_r; try lia.
      apply le_opp_mul_mul; try lia; apply twos_complement_max. }
    symmetry; apply div_bet_1; split; simpl; lia.
  - rewrite BinInt.Z.ltb_ge in ltm.
    unfold nat_bitvector_big; change (hd (?x :: _)) with x.
    replace (_ / _) with 0. { reflexivity. }
    symmetry; apply div_small.
    rewrite <- Znat.Nat2Z.id, <- Znat.Z2Nat.inj_lt; try lia.
    rewrite <- Z_inj_pow, Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
    rewrite <- BinInt.Z.pow_add_r, Heqm, BinInt.Z.pow_add_r; try lia.
    apply lt_mul_mul; try lia; apply twos_complement_max.
Qed.

(* Computes the upper n bits of the signed multiplication
   of two two's-complement numbers.

  Output is the sign of product (in first bit) followed
  by the upper bits of the absolute-value of the product.

  This means that, for example, -1 * 1 will result in
  10...0, which is NOT representing a twos complement 
  number.
*)
Definition bv_smulh : forall {n} (b1 b2 : t bool (S n)), 
                                 t bool (S n).
  intros n b1 b2.
  apply twos_complement in b1, b2.
  remember (mul b1 b2) as b12.
  apply cons.
  - exact (ltb b12 Z0).
  - apply (fun (x : t bool (n + n)) => fst (splitat n x)), 
          nat_bitvector_big, Z.abs_nat, b12.
Defined.

Theorem bv_smulh_correct_value :
  forall {n} (b1 b2 : t bool (S n)), 
  tl (bv_smulh b1 b2) = 
    fst (splitat n (nat_bitvector_big (n + n) 
    (Z.abs_nat (mul (twos_complement b1) (twos_complement b2))))).
Proof. reflexivity. Qed.

Theorem bv_smulh_correct_sign :
  forall {n} (b1 b2 : t bool (S n)), 
  lt (opp (pow 2 (of_nat n))) (twos_complement b1) -> 
  lt (opp (pow 2 (of_nat n))) (twos_complement b2) -> 
  hd (bv_smulh b1 b2) = hd (bv_smul b1 b2).
Proof.
  intros.
  assert (lt (twos_complement b2) (pow 2 (of_nat n))).
  { apply twos_complement_max. }
  assert (lt (twos_complement b3) (pow 2 (of_nat n))).
  { apply twos_complement_max. }
  unfold bv_smulh; simpl.
  rewrite <- (twos_complement_sign (n + n)); try reflexivity;
  rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
  - apply le_opp_mul_mul; lia.
  - apply lt_mul_mul; lia.
Qed.
