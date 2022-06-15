From Coq Require Import
  Lia Nat BinPos Pnat BinNat BinIntDef
  ZArith.Int NArith.Nnat Numbers.BinNums 
  ProofIrrelevance 
  List VectorDef VectorEq.
Import PeanoNat.Nat(add_comm,
                    lt_neq,
                    div_mod,
                    add_0_r,
                    eqb_neq,
                    mod_small, mod_upper_bound,
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

Definition bitValN (b : bool) : N :=
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
  proj1_sig (bitVal n) = N.to_nat (bitValN n).
Proof. intros []; reflexivity. Qed.

Definition Byte := t bool 8.

Definition zeroByte : Byte :=
  const b0 8.

Definition oneByte : Byte :=
  const b1 8.

Definition iffb (b1 v2 : bool) : bool :=
  match b1, v2 with
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

Definition bv_and {n} (v1 v2 : t bool n) : t bool n :=
  map2 andb v1 v2.

Definition bv_or {n} (v1 v2 : t bool n) : t bool n :=
  map2 orb v1 v2.

Definition bv_xor {n} (v1 v2 : t bool n) : t bool n :=
  map2 xorb v1 v2.

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

Definition bitvector_nat_little {n} (v : t bool n) : nat :=
  proj1_sig (bitvector_fin_little v).

Fixpoint nat_bitvector_little (n m : nat) : t bool n :=
  match n with
  | 0 => nil bool
  | S n => 
    cons _ (negb (m mod 2 =? 0)) _ (nat_bitvector_little n (m / 2))
  end.

Definition fin_bitvector_little {n} (f : fin (2 ^ n)) : t bool n :=
  nat_bitvector_little n (proj1_sig f).

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
    simpl proj1_sig.
    unfold nat_bitvector_little; fold nat_bitvector_little.
    replace (S (f + (f + 0))) with (1 + f * 2); [| lia].
    replace (((1 + f * 2)) mod 2) with 1.
    2: { rewrite PeanoNat.Nat.mod_add; [ reflexivity | lia ]. }
    replace ((1 + f * 2) / 2) with f.
    2: { rewrite PeanoNat.Nat.div_add; [ reflexivity | lia ]. }
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
    simpl proj1_sig.
    unfold nat_bitvector_little; fold nat_bitvector_little.
    replace (f + (f + 0)) with (f * 2);[|lia].
    replace (f * 2 / 2) with f.
    2: { rewrite PeanoNat.Nat.div_mul; [ reflexivity | lia ]. }
    replace ((f * 2) mod 2) with 0.
    2: { symmetry. rewrite PeanoNat.Nat.mod_mul; [ reflexivity | lia ]. } 
    reflexivity.
Qed.

Theorem bitvector_fin_little_inv : forall {n} (v : t bool n),
  fin_bitvector_little (bitvector_fin_little v) = v.
Proof.
  intros n v.
  induction v;[reflexivity|].
  - destruct h; simpl bitvector_fin_little.
    + rewrite bitvector_fin_little_inv_lem_true.
      rewrite IHv.
      reflexivity.
    + rewrite bitvector_fin_little_inv_lem_false.
      rewrite IHv.
      reflexivity.
Qed.

Theorem bitvector_nat_little_inv :
  forall n (v : t bool n),
    nat_bitvector_little n (bitvector_nat_little v) = v.
Proof.
  intros n v.
  unfold bitvector_nat_little.
  change (nat_bitvector_little n (proj1_sig ?x))
    with (fin_bitvector_little x).
  apply bitvector_fin_little_inv.
Qed.

Theorem fin_bitvector_little_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin_little (fin_bitvector_little f) = f.
Proof.
  intro n.
  induction n as [|n IHn]; intros [f fprp].
  - simpl.
    rewrite unique_f0.
    apply subset_eq_compat.
    reflexivity.
  - unfold fin_bitvector_little.
    unfold nat_bitvector_little; fold nat_bitvector_little.
    assert (f = (2 * (f / 2) + f mod 2)) as fsplit.
    { rewrite <- div_mod; [ reflexivity | lia ]. }
    assert (f/2 < 2 ^ n) as fhprp.
    { apply PeanoNat.Nat.div_lt_upper_bound;[lia|]. exact fprp. } 
    assert (bitvector_fin_little (fin_bitvector_little (exist _ (f/2) fhprp)) 
            = (exist _ (f/2) fhprp));[apply IHn|];clear IHn.
    unfold proj1_sig.
    destruct (f mod 2 =? 0) eqn:fmod;
    simpl bitvector_fin_little; simpl in H;
    unfold  fin_bitvector_little, proj1_sig in H; rewrite H; clear H; simpl;
    apply subset_eq_compat;
    replace (fst (divmod f 1 0 1)) with (f / 2); try reflexivity.
    + rewrite eqb_eq in fmod.
      rewrite fmod, add_0_r in fsplit.
      lia.
    + replace (f mod 2) with 1 in fsplit;[lia|].
      rewrite eqb_neq in fmod.
      destruct (mod_2_0or1 f);[destruct (fmod H)|].
      symmetry; assumption.
Qed.

Theorem nat_bitvector_little_inv :
  forall {n} k, k < 2 ^ n ->
    bitvector_nat_little (nat_bitvector_little n k) = k.
Proof.
  intros n k klt.
  change k with (proj1_sig (mk_fin k klt)).
  unfold bitvector_nat_little.
  change (nat_bitvector_little n (proj1_sig ?x))
    with (fin_bitvector_little x).
  rewrite fin_bitvector_little_inv.
  reflexivity.
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
  induction v;[reflexivity|].
  assert (bitvector_nat_big v < 2 ^ n).
  { apply bitvector_nat_big_lt_2pow. }
  rewrite bitvector_nat_big_cons.
  unfold nat_bitvector_big; fold nat_bitvector_big.
  f_equal.
  - destruct (bitvector_fin_big v); destruct h; simpl proj1_sig.
    + rewrite PeanoNat.Nat.mul_1_l.
      replace (_ / _) with 1; [ reflexivity | ].
      symmetry; apply div_bet_1; lia.
    + rewrite PeanoNat.Nat.mul_0_l, div_small; simpl; lia.
  - assert (2 ^ n <> 0) as pow0.
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
    + simpl. rewrite add_0_r, PeanoNat.Nat.mod_same; trivial.
    + simpl; rewrite mod_small; [ reflexivity | ].
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
      rewrite mod_small; [ reflexivity | ].
      rewrite <- PeanoNat.Nat.div_small_iff; assumption.
    + rewrite eqb_neq in fDiv0.
      rewrite (div_mod f (2 ^ n)) at 2;[|assumption].
      rewrite PeanoNat.Nat.add_comm.
      f_equal.
      replace (f / 2 ^ n) with 1. { rewrite PeanoNat.Nat.mul_1_r; reflexivity. }
      symmetry.
      apply div_bet_1. 
      split;[|assumption].
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

Theorem nat_bitvector_big_inj : forall {n m o},
  m < 2 ^ n -> o < 2 ^ n ->
  nat_bitvector_big n m = nat_bitvector_big n o <-> m = o.
Proof.
  intros; split; intro.
  - apply (f_equal bitvector_nat_big) in H1.
    rewrite nat_bitvector_big_inv in H1;
    rewrite nat_bitvector_big_inv in H1; auto.
  - f_equal; auto.
Qed.

Theorem bitvector_nat_big_inj : forall {n} {m o : t bool n},
  bitvector_nat_big m = bitvector_nat_big o <-> m = o.
Proof.
  intros; split; intro.
  - apply (f_equal (nat_bitvector_big n)) in H.
    rewrite bitvector_nat_big_inv in H;
    rewrite bitvector_nat_big_inv in H; auto.
  - f_equal; auto.
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
  bv_eq v (VectorDef.const b0 n) =
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

Theorem bv_eq_big_conv : forall k n m,
  n < 2 ^ k -> m < 2 ^ k ->
  bv_eq (nat_bitvector_big k n)
        (nat_bitvector_big k m) =
  (n =? m).
Proof.
  intros.
  destruct (n =? m) eqn:nqVal.
  - rewrite eqb_eq in nqVal.
    rewrite nqVal, bv_eq_equiv.
    rewrite nat_bitvector_big_inj; auto.
  - destruct (bv_eq _ _) eqn:bvVal.
    + rewrite bv_eq_equiv in bvVal.
      rewrite nat_bitvector_big_inj in bvVal; try assumption.
      rewrite bvVal, eqb_neq in nqVal.
      contradiction.
    + reflexivity.
Qed.

Theorem bitvector_fin_big_0_const :
  forall {n} (v : t bool n),
    (v = (VectorDef.const b0 n)) <-> (bitvector_nat_big v = 0).
Proof.
  intros n v.
  rewrite <- bv_eq_equiv, <- eqb_eq, <- Bool.eq_iff_eq_true.
  apply bitvector_fin_big_0_0.
Qed.

Theorem bitvector_fin_big_1_const :
  forall {n} (v : t bool n),
    (v = (VectorDef.const b1 n)) <-> (bitvector_nat_big v = pred (2 ^ n)).
Proof.
  intros n v.
  induction v.
  - split; reflexivity.
  - simpl; rewrite bitvector_nat_big_cons; split.
    + intro H; injection H; intros H0 H1; apply inj_pair2 in H0; clear H.
      rewrite IHv in H0; rewrite H0, H1.
      simpl; lia.
    + intro H.
      replace (pred (2 ^ n + (2 ^ n + 0)))
         with (2 ^ n + pred (2 ^ n)) in H;[|lia].
      assert (bitvector_nat_big v < 2 ^ n).
      { apply bitvector_nat_big_lt_2pow. }
      destruct h; simpl in H;[|lia].
      f_equal.
      rewrite IHv; lia.
Qed.

(* Encodings using binary numbers *)

Fixpoint positive_list_little (m : positive) : list bool :=
  match m with
  | xH => List.cons b1 List.nil
  | xO p => List.cons b0 (positive_list_little p)
  | xI p => List.cons b1 (positive_list_little p)
  end.

Fixpoint positive_bitvector_little (n : nat) (m : positive) : t bool n :=
  match n return t bool n with
  | 0 => []
  | S n =>
    match m with
    | xH => b1 :: const b0 _
    | xO p => b0 :: positive_bitvector_little n p
    | xI p => b1 :: positive_bitvector_little n p
    end
  end.

Definition N_bitvector_little (n : nat) (m : N) : t bool n :=
  match m with
  | N0 => const b0 _
  | Npos p => positive_bitvector_little _ p
  end.

Fixpoint bitvector_N_little {n : nat} (v : t bool n) : N :=
  match v with
  | [] => N0
  | hd :: tl => 
    match hd with
    | true => BinPosDef.Pos.Nsucc_double (bitvector_N_little tl)
    | false => BinPosDef.Pos.Ndouble (bitvector_N_little tl)
    end
  end.

Fixpoint positive_len (p : positive): nat :=
  match p with
  | xH => 0
  | xO p => S (positive_len p)
  | xI p => S (positive_len p)
  end.

Definition N_len (n : N): nat :=
  match n with
  | N0 => 0
  | Npos n => S (positive_len n)
  end.

Theorem double_Sn_Pos : forall n,
  exists p, 
    BinPosDef.Pos.Nsucc_double n = Npos p.
Proof.
  intros n.
  destruct n.
  - exists xH; reflexivity.
  - exists (xI p); reflexivity.
Qed.

Theorem double_Sn_N0 : forall n,
  BinPosDef.Pos.Nsucc_double n = N0 ->
  n = N0.
Proof.
  intros.
  destruct n;[reflexivity|].
  cbn in H; discriminate H. 
Qed.

Theorem double_n_N0 : forall n,
  BinPosDef.Pos.Ndouble n = N0 ->
  n = N0.
Proof.
  intros.
  destruct n;[reflexivity|].
  cbn in H; discriminate H. 
Qed.

Theorem n0_list_nil {n : nat} (v : t bool n) :
  bitvector_N_little v = N0 -> v = const b0 _.
Proof.
  induction v;[reflexivity|].
  unfold bitvector_N_little; fold (bitvector_N_little (n := n)).
  destruct h; intro.
  - destruct (double_Sn_Pos (bitvector_N_little v)).
    rewrite H0 in H.
    discriminate H.
  - apply double_n_N0 in H.
    rewrite (IHv H).
    reflexivity.
Qed.

Theorem bitvector_N_little_inv {n : nat} : forall (v : t bool n),
  N_bitvector_little n (bitvector_N_little v) = v.
Proof.
  induction v;[reflexivity|].
  destruct h; simpl; unfold N_bitvector_little;
  remember (bitvector_N_little v) as bNlv;
  destruct bNlv; unfold BinPosDef.Pos.Nsucc_double;
  unfold positive_bitvector_little; simpl; f_equal;
  try exact IHv.
Qed.

Theorem bitvector_N_little_inj {n : nat} : forall (v u : t bool n),
  bitvector_N_little v = bitvector_N_little u <-> v = u.
Proof.
  intros; split; intro.
  - rewrite <- (bitvector_N_little_inv v).
    rewrite <- (bitvector_N_little_inv u).
    rewrite H; reflexivity.
  - rewrite H; reflexivity.
Qed.

Theorem bitvector_N_little_const_N0 : forall n,
  bitvector_N_little (const b0 n) = N0.
Proof.
  induction n.
  - reflexivity.
  - cbn; rewrite IHn; reflexivity.
Qed.

Theorem N_bitvector_little_inv {n : nat} : forall (m : N),
  N_len m <= n ->
  bitvector_N_little (N_bitvector_little n m) = m.
Proof.
  intros.
  destruct m. 
  - unfold N_bitvector_little.
    apply bitvector_N_little_const_N0.
  - unfold N_bitvector_little.
    unfold N_len in H.
    generalize dependent n.
    induction p; intros.
    + destruct n;[lia|cbn].
      rewrite IHp;[reflexivity|
      unfold positive_len in H; fold positive_len in H; lia].
    + destruct n;[lia|cbn].
      rewrite IHp;[reflexivity|
      unfold positive_len in H; fold positive_len in H; lia].
    + destruct n;[lia|cbn].
      rewrite bitvector_N_little_const_N0.
      reflexivity.
Qed.

Theorem N_bitvector_little_inj {n : nat} {k l : N} : 
  N_len k <= n -> N_len l <= n ->
  N_bitvector_little n k = N_bitvector_little n l <-> k = l.
Proof.
  intros; split; intro.
  - rewrite <- (N_bitvector_little_inv (n := n) k).
    rewrite <- (N_bitvector_little_inv (n := n) l).
    rewrite H1; reflexivity.
    all: assumption.
  - rewrite H1; reflexivity.
Qed.

Theorem N_bitvector_little_unfold:
  forall n k, 
  N_bitvector_little (S n) (N.of_nat (S k)) =
  (k mod 2 =? 0) :: N_bitvector_little n (N.of_nat (S k / 2)).
Proof.
  destruct k;[reflexivity|].
  destruct (k mod 2 =? 0) eqn:skmod2.
  - rewrite eqb_eq in skmod2. 
    assert (k = (2 * (k / 2)));[rewrite PeanoNat.Nat.div_exact;lia|].
    assert (S (S k) = (2 * (S (S k) / 2)));[
      change (S (S k)) with (1 * 2 + k) at 2;
      rewrite PeanoNat.Nat.div_add_l; lia|].
    rewrite H0 at 1.
    rewrite Nnat.Nat2N.inj_double.
    unfold N.double.
    assert (S (S k) / 2 = S (k / 2));[
      change (S (S k)) with (1 * 2 + k);
      rewrite PeanoNat.Nat.div_add_l; lia|].
    rewrite H1.
    unfold N.of_nat, N_bitvector_little, positive_bitvector_little;
    fold positive_bitvector_little.
    f_equal.
    change (S k) with (1 + k).
    rewrite <- PeanoNat.Nat.add_mod_idemp_r;[|lia].
    rewrite skmod2.
    reflexivity.
  - rewrite eqb_neq in skmod2.
    apply nmod_2_0 in skmod2. 
    assert (S k mod 2 = 0);[
      change (S k) with (1 + k);
      rewrite <- PeanoNat.Nat.add_mod_idemp_r; try lia;
      rewrite skmod2; reflexivity|].
    assert (S k = (2 * (S k / 2)));[rewrite PeanoNat.Nat.div_exact;lia|].
    rewrite H0 at 1.
    rewrite Nnat.Nat2N.inj_succ_double.
    destruct k;[lia|].
    assert (S (S k) / 2 = S (k / 2));[
      change (S (S k)) with (1 * 2 + k);
      rewrite PeanoNat.Nat.div_add_l; lia|].
    rewrite H1.
    unfold N.succ_double, N.of_nat at 1, N_bitvector_little at 1, positive_list_little.
    rewrite H; f_equal.
    unfold N_bitvector_little.
    assert (S (S (S k)) / 2 = S ((S k) / 2));[
      change (S (S (S k))) with (1 * 2 + (S k));
      rewrite PeanoNat.Nat.div_add_l; lia|].
    rewrite H2.
    unfold N.of_nat.
    rewrite mod_2_div;[reflexivity|].
    replace k with (2 mod 2 + k);[|reflexivity].
    rewrite PeanoNat.Nat.add_mod_idemp_l;[|lia].
    exact H.
Qed.

Theorem nat_bitvector_little_const :
  forall n, nat_bitvector_little n 0 = const b0 n.
Proof.
  intro n.
  induction n;[reflexivity|].
  unfold nat_bitvector_little; fold nat_bitvector_little.
  change (0 / 2) with 0.
  rewrite IHn; reflexivity.
Qed.

Theorem Nsucc_double_nat_val : 
  forall p, 
    N.to_nat (BinPosDef.Pos.Nsucc_double p) =
    S (2 * N.to_nat p).
Proof.
  destruct p;[reflexivity|].
  induction p;
  unfold BinPosDef.Pos.Nsucc_double;
  change 2 with (N.to_nat (Npos (xO xH)));
  rewrite <- Nnat.N2Nat.inj_mul;
  unfold N.mul;
  change (S (N.to_nat (Npos ?p)))
    with (BinPos.Pos.to_nat (BinPos.Pos.succ p));
  reflexivity.
Qed.

Theorem Ndouble_nat_val : 
  forall p, 
    N.to_nat (BinPosDef.Pos.Ndouble p) =
    2 * N.to_nat p.
Proof.
  destruct p;[reflexivity|].
  induction p;
  unfold BinPosDef.Pos.Ndouble;
  change 2 with (N.to_nat (Npos (xO xH)));
  rewrite <- Nnat.N2Nat.inj_mul;
  unfold N.mul;
  reflexivity.
Qed.

Theorem bitvector_N_little_max : forall n (v : t bool n), 
  N.to_nat (bitvector_N_little v) < 2 ^ n.
Proof.
  intros n v.
  induction v;[simpl; lia|].
  cbn; destruct h.
  - rewrite Nsucc_double_nat_val; lia.
  - rewrite Ndouble_nat_val; lia.
Qed.

Theorem N_nat_bitvector_little :
  forall n k, N_bitvector_little n (N.of_nat k) = nat_bitvector_little n k.
Proof.
  induction n;[destruct k;reflexivity|].
  intro k. 
  unfold nat_bitvector_little; fold nat_bitvector_little.
  destruct k.
  - cbn; rewrite nat_bitvector_little_const; reflexivity.
  - rewrite N_bitvector_little_unfold.
    rewrite <- IHn.
    f_equal.
    change (S k) with (1 + k).
    rewrite <- PeanoNat.Nat.add_mod_idemp_r;[|lia].
    destruct (k mod 2 =? 0) eqn:mVal.
    + rewrite eqb_eq in mVal.
      rewrite mVal; reflexivity.
    + rewrite eqb_neq in mVal.
      apply nmod_2_0 in mVal.
      rewrite mVal; reflexivity.
Qed.

Theorem N_len_max : forall n x,
  N_len x <= n <-> N.to_nat x < 2 ^ n.
Proof.
  intros n x; split; intro; generalize dependent n; destruct x.
  - intros.
    simpl.
    apply zero2pow.
  - induction p; intros; simpl in H; try simpl in IHp.
    + destruct n;[lia|].
      change (Npos (xI p))
        with (BinPosDef.Pos.Nsucc_double (Npos p)).
      rewrite Nsucc_double_nat_val; cbn.
      assert (BinPos.Pos.to_nat p < 2 ^ n);[apply IHp;lia|lia].
    + destruct n;[lia|].
      change (Npos (xO p))
        with (BinPosDef.Pos.Ndouble (Npos p)).
      rewrite Ndouble_nat_val; cbn.
      assert (BinPos.Pos.to_nat p < 2 ^ n);[apply IHp;lia|lia].
    + destruct n;[lia|].
      assert (0 < 2 ^ n);[apply Arith.zero2pow|].
      cbn; lia.
  - simpl; lia.
  - induction p; intros; try simpl in IHp.
    + change (Npos (xI p))
        with (BinPosDef.Pos.Nsucc_double (Npos p))
        in H.
      rewrite Nsucc_double_nat_val in H.
      destruct n;[simpl in H; lia|].
      simpl. cbn in H.
      assert (BinPos.Pos.to_nat p < 2 ^ n);[lia|].
      apply IHp in H0.
      lia.
    + change (Npos (xO p))
        with (BinPosDef.Pos.Ndouble (Npos p))
        in H.
      rewrite Ndouble_nat_val in H.
      destruct n;[simpl in H; lia|].
      simpl. cbn in H.
      assert (BinPos.Pos.to_nat p < 2 ^ n);[lia|].
      apply IHp in H0.
      lia.
    + destruct n;[simpl in H; lia|simpl; lia].
Qed.

Theorem N_len_max_2 : forall n x,
  N_len (N.of_nat x) <= n <-> x < 2 ^ n.
Proof.
  intros.
  rewrite <- (Nnat.Nat2N.id x) at 2.
  rewrite <- N_len_max.
  reflexivity.
Qed.

Theorem bitvector_N_nat_little :
  forall n (v : t bool n), 
  N.to_nat (bitvector_N_little v) = bitvector_nat_little v.
Proof.
  intros n v.
  apply Nnat.Nat2N.inj.
  rewrite Nnat.N2Nat.id.
  rewrite <- (N_bitvector_little_inj (n := n)).
  rewrite bitvector_N_little_inv, N_nat_bitvector_little, bitvector_nat_little_inv.
  reflexivity.
  rewrite N_len_max; apply bitvector_N_little_max.
  rewrite N_len_max.
  rewrite Nnat.Nat2N.id.
  unfold bitvector_nat_little.
  destruct (bitvector_fin_little v) as [f flt].
  simpl; assumption.
Qed.

Definition N_bitvector_big (n : nat) (m : N) : t bool n :=
  rev (N_bitvector_little n m).

Definition bitvector_N_big {n : nat} (v : t bool n) : N :=
  bitvector_N_little (rev v).

Theorem rev_nat_bitvector_little : 
  forall n k,
    k < 2 ^ n ->
    rev (nat_bitvector_little n k) =
    nat_bitvector_big n k.
Proof.
  intros.
  replace (nat_bitvector_little n k)
     with (fin_bitvector_little (mk_fin k H));[|reflexivity].
  rewrite rev_bitvector_fin, vector_rev_rev_id.
  reflexivity.
Qed.

Theorem N_nat_bitvector_big :
  forall n k, k < 2 ^ n ->
  N_bitvector_big n (N.of_nat k) = nat_bitvector_big n k.
Proof.
  intros n k lt.
  unfold N_bitvector_big.
  rewrite <- rev_nat_bitvector_little;[|assumption].
  f_equal.
  rewrite N_nat_bitvector_little.
  reflexivity.
Qed.

Theorem nat_N_bitvector_big :
  forall n m, N_len m <= n ->
  N_bitvector_big n m = nat_bitvector_big n (N.to_nat m).
Proof.
  intros n k lt.
  rewrite <- N_nat_bitvector_big, Nnat.N2Nat.id;[reflexivity|].
  rewrite <- N_len_max; assumption.
Qed.

Theorem bitvector_N_nat_big :
  forall n (v : t bool n),
  (N.to_nat (bitvector_N_big v)) = bitvector_nat_big v.
Proof.
  unfold bitvector_N_big.
  intros n k.
  rewrite bitvector_N_nat_little.
  unfold bitvector_nat_big, bitvector_nat_little.
  rewrite <- bitvector_fin_rev; reflexivity.
Qed.

Theorem bitvector_nat_N_big :
  forall n (v : t bool n),
  (bitvector_N_big v) = N.of_nat (bitvector_nat_big v).
Proof.
  intros.
  rewrite <- bitvector_N_nat_big, Nnat.N2Nat.id.
  reflexivity.
Qed.

(* Bitvector arithmetic *)

(*least significant bits of addition (unsigned)
  extra leading bit indicates an overflow*)
Definition bv_add {n} (v1 v2 : t bool n) : t bool (S n) :=
  N_bitvector_big (S n)
    (bitvector_N_big v1 + bitvector_N_big v2).

Theorem bv_add_correct_1 : forall {n} (v1 v2 : t bool n),
  bv_add v1 v2 = nat_bitvector_big (S n)
    (bitvector_nat_big v1 + bitvector_nat_big v2).
Proof.
  intros.
  unfold bv_add.
  repeat rewrite bitvector_nat_N_big.
  rewrite <- Nnat.Nat2N.inj_add, N_nat_bitvector_big;[reflexivity|].
  assert (bitvector_nat_big v1 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  assert (bitvector_nat_big v2 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  cbn; lia.
Qed.

Theorem bv_add_correct_2 : forall {n} (n1 n2 : nat),
  n1 < 2 ^ n -> n2 < 2 ^ n ->
  n1 + n2 = bitvector_nat_big (
  bv_add (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof.
  intros.
  unfold bv_add.
  repeat rewrite bitvector_nat_N_big.
  repeat rewrite nat_bitvector_big_inv.
  rewrite <- Nnat.Nat2N.inj_add, N_nat_bitvector_big, nat_bitvector_big_inv.
  all: cbn; lia.
Qed.

Theorem bv_add_correct_mod :
  forall {n : nat} (n1 n2 : nat),
  n1 < 2 ^ n ->
  n2 < 2 ^ n ->
  (n1 + n2) mod 2 ^ n =
  bitvector_nat_big
	(VectorDef.tl (bv_add (nat_bitvector_big n n1) (nat_bitvector_big n n2))).
Proof.
  intros.
  rewrite bv_add_correct_1.
  rewrite nat_bitvector_big_inv;[|assumption].
  rewrite nat_bitvector_big_inv;[|assumption].
  unfold nat_bitvector_big.
  simpl VectorDef.tl.
  fold nat_bitvector_big.
  rewrite nat_bitvector_big_inv;[reflexivity|].
  apply mod_upper_bound; lia.
Qed.

Theorem bv_add_correct_mod_2 :
  forall {n : nat} (n1 n2 : nat),
  n1 < 2 ^ n ->
  n2 < 2 ^ n ->
  nat_bitvector_big _ ((n1 + n2) mod 2 ^ n) =
	VectorDef.tl (bv_add (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof.
  intros; rewrite bv_add_correct_1.
  apply nat_bitvector_big_inj;try (apply mod_upper_bound; lia).
  rewrite nat_bitvector_big_inv;[|assumption].
  rewrite nat_bitvector_big_inv;[|assumption].
  reflexivity.
Qed.

(*least significant bits of subtraction (unsigned). 
  extra leading bit indicates a borrow, 0 if borrow, 1 if not.*)
Definition bv_sub {n} (v1 v2 : t bool n) : t bool (S n) :=
  N_bitvector_big (S n) 
    (bitvector_N_big v1 + 2 ^ N.of_nat n - bitvector_N_big v2).

Theorem bv_sub_correct_1 : forall {n} (v1 v2 : t bool n),
  bv_sub v1 v2 = nat_bitvector_big (S n) 
    (bitvector_nat_big v1 + 2 ^ n - bitvector_nat_big v2).
Proof.
  intros.
  unfold bv_sub.
  change (2)%N with (N.of_nat 2).
  rewrite <- Nat2N_inj_pow.
  repeat rewrite bitvector_nat_N_big.
  rewrite <- Nnat.Nat2N.inj_add, <- Nnat.Nat2N.inj_sub, N_nat_bitvector_big.
  reflexivity.
  assert (bitvector_nat_big v1 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  assert (bitvector_nat_big v2 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  cbn; lia.
Qed.

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

Theorem bv_sub_correct_pos : 
  forall k n m,
  n < 2 ^ k -> m < 2 ^ k -> m <= n ->
  VectorDef.tl (bv_sub (nat_bitvector_big k n)
            (nat_bitvector_big k m))
  = nat_bitvector_big k (n - m).
  intros k n m nlt mlt le.
  rewrite bv_sub_correct_1.
  unfold nat_bitvector_big; fold nat_bitvector_big.
  simpl; f_equal.
  repeat rewrite nat_bitvector_big_inv; try assumption.
  rewrite PeanoNat.Nat.add_sub_swap; [ | assumption ].
  rewrite <- PeanoNat.Nat.add_mod_idemp_r; [| apply PeanoNat.Nat.pow_nonzero; lia].
  rewrite PeanoNat.Nat.mod_same; [| apply PeanoNat.Nat.pow_nonzero; lia].
  rewrite add_0_r.
  rewrite mod_small; lia.
Qed.

(*least significant bits of multiplication (unsigned)
  additional bits indicate, respecively, an overflow and a result of 0.
  Left vector are MSB, right vector are LSB.*)
Definition bv_mul_flags {n} (v1 v2 : t bool n) : bool * bool * t bool n * t bool n :=
  let prod := (bitvector_N_big v1 * bitvector_N_big v2)%N in
  let (pvH, pvL) := splitat n (N_bitvector_big (n + n) prod) in
  (2 ^ N.of_nat n <=? prod, prod =? 0, pvH, pvL)%N.

(*Multiplication (unsigned), all bits*)
Definition bv_mul {n} (v1 v2 : t bool n) : t bool (n + n) :=
  (fun x => snd (fst x) ++ snd x) (bv_mul_flags v1 v2).

Theorem bv_mul_correct_1 : forall {n} (v1 v2 : t bool n),
  bv_mul v1 v2 = nat_bitvector_big (n + n) 
    (bitvector_nat_big v1 * bitvector_nat_big v2).
Proof.
  intros n v2 v3.
  unfold bv_mul, bv_mul_flags.
  destruct (splitat n _) eqn:splitEq; simpl.
  apply VectorSpec.append_splitat in splitEq.
  rewrite <- splitEq.
  repeat rewrite bitvector_nat_N_big.
  rewrite <- Nnat.Nat2N.inj_mul, N_nat_bitvector_big;[reflexivity|].
  assert (bitvector_nat_big v2 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  assert (bitvector_nat_big v3 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  rewrite PeanoNat.Nat.pow_add_r.
  apply PeanoNat.Nat.mul_lt_mono; lia.
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

Theorem bv_mullh_correct : forall {n} (v1 v2 : t bool n),
  splitat n (bv_mul v1 v2) = 
    ( nat_bitvector_big n (bitvector_nat_big v1 * bitvector_nat_big v2 / 2 ^ n)
    , nat_bitvector_big n (bitvector_nat_big v1 * bitvector_nat_big v2 mod 2 ^ n)).
Proof.
  intros n v2 v3.
  rewrite bv_mul_correct_1.
  destruct (splitat n (nat_bitvector_big _ _)) eqn:splitEq; simpl.
  apply VectorSpec.append_splitat in splitEq.
  assert (bitvector_nat_big v2 < 2 ^ n).
  { apply bitvector_nat_big_lt_2pow. }
  assert (bitvector_nat_big v3 < 2 ^ n).
  { apply bitvector_nat_big_lt_2pow. }
  replace (bitvector_nat_big v2 * bitvector_nat_big v3)
     with (bitvector_nat_big t * 2 ^ n + bitvector_nat_big t0).
  - f_equal.
    + replace (_ / _) with (bitvector_nat_big t).
      { symmetry; apply bitvector_nat_big_inv. }
      rewrite PeanoNat.Nat.div_add_l.
      2: { apply PeanoNat.Nat.pow_nonzero; lia. }
      rewrite div_small. { lia. }
      apply bitvector_nat_big_lt_2pow.
    + rewrite <- PeanoNat.Nat.add_mod_idemp_l, PeanoNat.Nat.mod_mul;
      try (apply PeanoNat.Nat.pow_nonzero; lia).
      simpl; rewrite mod_small. 2:{ apply bitvector_nat_big_lt_2pow. }
      symmetry; apply bitvector_nat_big_inv.
  - symmetry; rewrite <- (nat_bitvector_big_inv (n + n) (_ * _)). 
    + rewrite splitEq; apply bitvector_nat_big_app.
    + rewrite PeanoNat.Nat.pow_add_r; apply PeanoNat.Nat.mul_lt_mono; 
      assumption.
Qed.

Theorem lt_mul_cap : 
  forall a b c, 0 < c -> a + b * c < c -> b = 0.
Proof.
  intros.
  assert (b * c < 1 * c) as bclt. { lia. }
  rewrite <- PeanoNat.Nat.mul_lt_mono_pos_r in bclt; lia.
Qed.

Theorem bv_mull_high_const0 : forall {n} (v1 v2 : t bool n),
  (bitvector_nat_big v1 * bitvector_nat_big v2 < 2 ^ n)
  <-> (fst (splitat n (bv_mul v1 v2)) = const b0 _).
Proof.
  intros n v1 v2.
  rewrite <- nat_bitvector_big_inv at 1.
  2: { rewrite PeanoNat.Nat.pow_add_r.
       apply PeanoNat.Nat.mul_lt_mono;
       apply bitvector_nat_big_lt_2pow. }
  rewrite <- bv_mul_correct_1.
  destruct (splitat _ _) as [v12h v12l] eqn:sE; simpl fst.
  apply VectorSpec.append_splitat in sE; rewrite sE.
  rewrite bitvector_nat_big_app.
  split.
  - intro; rewrite bitvector_fin_big_0_const.
    rewrite add_comm in H. apply lt_mul_cap in H; lia.
  - intro H; rewrite bitvector_fin_big_0_const in H.
    rewrite H; simpl.
    apply bitvector_nat_big_lt_2pow.
Qed.

(*unsigned division. Extra boolean indicates division by 0.*)
Definition bv_udiv_flag {n} (v1 v2 : t bool n) : bool * t bool n :=
  let den := bitvector_N_big v2 in
  let b := (den =? 0)%N in
  (b, N_bitvector_big n (if b then 0 else (bitvector_N_big v1 / den))%N).

Definition bv_udiv {n} (v1 v2 : t bool n) : t bool n :=
  snd (bv_udiv_flag v1 v2).

(*"""
If [A]u = 0, then aW-1 · · · a0 = 0W .
"""*)
Theorem bv_udiv_correct_0 : forall {n} (v1 v2 : t bool n),
  bitvector_nat_big v2 = 0 ->
  bv_udiv v1 v2 = nat_bitvector_big n 0.
Proof.
  intros.
  unfold bv_udiv, bv_udiv_flag, snd.
  rewrite bitvector_nat_N_big, H.
  simpl.
  rewrite nat_N_bitvector_big;[reflexivity|simpl;lia].
Qed.

Theorem bv_udiv_correct_1 : forall {n} (v1 v2 : t bool n),
  bitvector_nat_big v2 > 0 ->
  bv_udiv v1 v2 = nat_bitvector_big n 
    (bitvector_nat_big v1 / bitvector_nat_big v2).
Proof.
  intros n v2 v3 v2LT.
  unfold bv_udiv, bv_udiv_flag.
  unfold snd.
  assert (bitvector_N_big v3 > 0)%N;[rewrite bitvector_nat_N_big; lia|].
  assert (bitvector_N_big v3 =? 0 = false)%N;[rewrite N.eqb_neq; lia|].
  rewrite H0.
  repeat rewrite bitvector_nat_N_big.
  rewrite <- Nat2N_inj_div, N_nat_bitvector_big;try lia; try reflexivity.
  assert (bitvector_nat_big v2 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  assert (bitvector_nat_big v3 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  apply neq0_div_lt; lia.
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
  rewrite nat_bitvector_big_inv; lia.
Qed.

(*unsigned modulus. Extra boolean indicates modulus by 0.*)
Definition bv_umod_flag {n} (v1 v2 : t bool n) : bool * t bool n :=
  let bas := bitvector_N_big v2 in
  let b := (bas =? 0)%N in
  (b, N_bitvector_big n (if b then 0 else bitvector_N_big v1 mod bas)%N).

Definition bv_umod {n} (v1 v2 : t bool n) : t bool n :=
  snd (bv_umod_flag v1 v2).

(*"""
If [A]u = 0, then aW-1 · · · a0 = 0W .
"""*)
Theorem bv_umod_correct_0 : forall {n} (v1 v2 : t bool n),
  bitvector_nat_big v2 = 0 ->
  bv_umod v1 v2 = nat_bitvector_big n 0.
Proof.
  intros.
  unfold bv_umod, bv_umod_flag, snd.
  rewrite bitvector_nat_N_big, H.
  simpl.
  rewrite nat_N_bitvector_big;[reflexivity|simpl;lia].
Qed.

Theorem bv_umod_correct_1 : forall {n} (v1 v2 : t bool n),
  bitvector_nat_big v2 > 0 ->
  bv_umod v1 v2 = nat_bitvector_big n 
    (bitvector_nat_big v1 mod bitvector_nat_big v2).
Proof.
  intros n v2 v3.
  unfold bv_umod, bv_umod_flag.
  unfold snd. intro.
  assert (bitvector_N_big v3 > 0)%N;[rewrite bitvector_nat_N_big; lia|].
  assert (bitvector_N_big v3 =? 0 = false)%N;[rewrite N.eqb_neq; lia|].
  rewrite H1.
  repeat rewrite bitvector_nat_N_big.
  rewrite <- Nat2N_inj_mod, N_nat_bitvector_big;try lia; try reflexivity.
  assert (bitvector_nat_big v2 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  assert (bitvector_nat_big v3 < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  transitivity (bitvector_nat_big v3);[|assumption].
  apply mod_upper_bound; lia.
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
  rewrite nat_bitvector_big_inv; lia.
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
  rewrite cast_app_l, VectorSpec.splitat_append.
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
  rewrite VectorSpec.splitat_append.
  simpl; vector_simp.
  f_equal; apply proof_irrelevance.
Qed.

(* two's complement signed integer representation. *)

Fixpoint twos_complement' {n} (v : t bool n) : N :=
  match v with
  | [] => 0
  | x :: xs => bitValN x * (2 ^ (N.of_nat n - 1)) + twos_complement' xs
  end.

Definition twos_complement {n} (v : t bool (S n)) : Z :=
  match v with
  | x :: xs => sub (Z.of_N (twos_complement' xs))
                   (Z.of_N (bitValN x * (2 ^ N.of_nat n)))
  end.

Theorem twos_complement_big : forall {n} (v : t bool n),
  twos_complement' v = N.of_nat (bitvector_nat_big v).
Proof.
  intros n v; induction v.
  - reflexivity.
  - change (twos_complement' (?x :: ?xs))
      with (bitValN x * (2 ^ (N.of_nat (S n) - 1)) + twos_complement' xs)%N.
    unfold bitvector_nat_big.
    rewrite bitvector_fin_big_cons.
    rewrite proj1_fin_cast, proj1_fin_add, proj1_fin_mul,
            proj1_fin_max, proj1_bitVal.
    rewrite Nat2N.inj_add, Nat2N.inj_mul, N2Nat.id.
    f_equal.
    + rewrite Nat2N_inj_pow; do 2 f_equal.
      lia.
    + exact IHv.
Qed.

Theorem twos_complement_n_big : forall {n} (v : t bool n),
  twos_complement' v = bitvector_N_big v.
Proof.
  intros n v.
  rewrite bitvector_nat_N_big.
  apply twos_complement_big.
Qed.

Theorem twos_complement_min : forall {n} (v : t bool (S n)),
  le (opp (pow 2 (of_nat n))) (twos_complement v).
Proof.
  intros n v.
  rewrite <- BinInt.Z.sub_0_l.
  rewrite (VectorSpec.eta v).
  simpl twos_complement.
  apply BinInt.Z.sub_le_mono;[lia|].
  destruct (hd v).
  2: { simpl bitValN; rewrite N.mul_0_l.
       apply BinInt.Z.pow_nonneg; lia. }
  simpl bitValN; rewrite N.mul_1_l.
  change (Zpos (xO xH)) with (of_nat 2).
  rewrite Z_inj_pow.
  change (Npos (xO xH)) with (N.of_nat 2).
  rewrite <- Nat2N_inj_pow, Znat.nat_N_Z.
  lia.
Qed.

Theorem twos_complement_max : forall {n} (v : t bool (S n)),
  lt (twos_complement v) (pow 2 (of_nat n)).
Proof.
  intros n v.
  rewrite (VectorSpec.eta v).
  simpl twos_complement.
  rewrite (BinInt.Zminus_0_l_reverse (pow _ _)).
  apply BinInt.Z.sub_lt_le_mono;[|lia].
  change (Zpos (xO xH)) with (of_nat 2).
  rewrite Z_inj_pow.
  rewrite twos_complement_big, Znat.nat_N_Z.
  apply Znat.inj_lt.
  apply bitvector_nat_big_lt_2pow.
Qed.

Definition twos_complement_inv (n : nat) (z : Z) : t bool (S n) :=
  match ltb z 0 with
  | true => N_bitvector_big _ (Z.to_N (add z (pow 2 (of_nat (S n)))))
  | false => N_bitvector_big _ (Z.to_N z)
  end.

Theorem twos_complement_iso_1 : forall {n} (v : t bool (S n)),
  twos_complement_inv n (twos_complement v) = v.
Proof.
  intros n v.
  assert (bitvector_nat_big (tl v) < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  rewrite (VectorSpec.eta v).
  simpl.
  rewrite twos_complement_big, Znat.nat_N_Z.
  change (Npos (xO xH)) with (N.of_nat 2).
  rewrite <- Nat2N_inj_pow.
  unfold twos_complement_inv.
  destruct (hd v); simpl bitValN.
  - change (Npos xH) with (N.of_nat 1).
    rewrite <- Nat2N.inj_mul, Znat.nat_N_Z.
    rewrite PeanoNat.Nat.mul_1_l, <- opp_sub_swap, <- Znat.Nat2Z.inj_sub.
    2: { apply PeanoNat.Nat.lt_le_incl; assumption. }
    unfold twos_complement_inv.
    replace (ltb _ 0) with true.
    2: { symmetry; rewrite Z_ltb_lt, BinInt.Z.opp_neg_pos.
         change Z0 with (of_nat 0). apply Znat.inj_lt; lia. }
    rewrite Znat.Nat2Z.inj_sub;[|lia].
    rewrite opp_sub_swap.
    rewrite <- BinInt.Z.sub_sub_distr, <- (opp_sub_swap (pow _ _) _).
    change (Zpos _) with (of_nat 2).
    rewrite Z_inj_pow, <- Znat.Nat2Z.inj_sub;[|simpl; lia].
    replace (2 ^ S n - 2 ^ n) with (2 ^ n);[|simpl; lia].
    rewrite BinInt.Z.sub_opp_r, <- Znat.Nat2Z.inj_add.
    rewrite <- Znat.nat_N_Z, Znat.N2Z.id, N_nat_bitvector_big;[|simpl; lia].
    cbn; f_equal.
    + replace (_ / _) with 1; [ reflexivity | ].
      symmetry; apply div_bet_1; lia.
    + assert (2 ^ n <> 0).
      { apply PeanoNat.Nat.pow_nonzero; lia. }
      rewrite <- PeanoNat.Nat.add_mod_idemp_r;[|assumption].
      rewrite PeanoNat.Nat.mod_same;[|assumption].
      rewrite add_0_r, mod_small;[|assumption].
      apply bitvector_nat_big_inv.
  - simpl of_nat; rewrite BinInt.Z.sub_0_r.
    replace (ltb _ 0) with false.
    2: { symmetry; rewrite Z_nltb_ge. apply Znat.Nat2Z.is_nonneg. }
    rewrite <- Znat.nat_N_Z, Znat.N2Z.id, N_nat_bitvector_big;[|simpl; lia].
    cbn; f_equal.
    + replace (_ / _) with 0; [ reflexivity | ].
      symmetry; apply div_small; assumption.
    + replace (_ mod _) with (bitvector_nat_big (tl v)).
      2: { symmetry; apply mod_small; assumption. }
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
    assert (0 < to_nat (opp z));[lia|].
    rewrite BinInt.Z.add_comm, <- BinInt.Z.sub_opp_r.
    rewrite nat_N_bitvector_big.
    2:{ rewrite N_len_max, Znat.Z_N_nat.
        rewrite Znat.Z2Nat.inj_sub;[|lia].
        rewrite Z2_inj_pow;[|lia|lia].
        rewrite Znat.Nat2Z.id.
        change (to_nat 2) with 2.
        apply PeanoNat.Nat.sub_lt;[|lia].
        rewrite opp_le_swap_l in lez.
        assert (to_nat (opp z) <= 2 ^ n);[|simpl;lia].
        rewrite Znat.Z2Nat.inj_le in lez;[|lia|lia].
        rewrite Z2_inj_pow in lez;[|lia|lia].
        rewrite Znat.Nat2Z.id in lez.
        exact lez. }
    rewrite Znat.Z_N_nat, Znat.Z2Nat.inj_sub;[|lia].
    rewrite Z2_inj_pow; try lia.
    change (to_nat _) with 2 at 1.
    rewrite Znat.Nat2Z.id.
    unfold nat_bitvector_big, twos_complement;
    fold nat_bitvector_big.
    rewrite twos_complement_big, Znat.nat_N_Z. 
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
    rewrite nat_bitvector_big_inv;[|lia].
    rewrite Znat.N2Z.inj_mul, Znat.N2Z.inj_pow, Znat.nat_N_Z.
    simpl BinInt.Z.of_N.
    rewrite Znat.Nat2Z.inj_sub;[|lia].
    rewrite <- Z_inj_pow; lia.
  - rewrite Z_nltb_ge in ltz0.
    assert (0 <= to_nat z);[lia|].
    assert (to_nat z < 2 ^ n).
    { rewrite Znat.Z2Nat.inj_lt, Z2_inj_pow, Znat.Nat2Z.id in ltz; try lia.
      assumption. }
    rewrite nat_N_bitvector_big.
    2:{ rewrite N_len_max, Znat.Z_N_nat; simpl; lia. }
    unfold nat_bitvector_big; fold nat_bitvector_big.
    rewrite mod_small, div_small; try lia.
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
    assert ((to_nat (opp z)) <= 2 ^ n).
    { rewrite <- Znat.Nat2Z.id, <- Znat.Z2Nat.inj_le; try lia;
      rewrite opp_le_swap_l, <- Z_inj_pow; lia. }
    rewrite nat_N_bitvector_big.
    2: { rewrite N_len_max, Znat.Z_N_nat.
         change 2%Z with (of_nat 2); rewrite Z_inj_pow.
         simpl; lia. }
    rewrite Znat.Z_N_nat.
    unfold nat_bitvector_big; replace (_ / _) with 1; [ reflexivity | ].
    rewrite BinInt.Z.add_comm, <- BinInt.Z.sub_opp_r.
    rewrite Znat.Z2Nat.inj_sub;[|lia].
    rewrite Z2_inj_pow; try lia.
    change (to_nat _) with 2 at 1.
    rewrite Znat.Nat2Z.id.
    symmetry; apply div_bet_1; simpl; lia.
  - rewrite Z_nltb_ge in ltz0.
    assert (to_nat z < 2 ^ n).
    { rewrite Znat.Z2Nat.inj_lt, Z2_inj_pow, Znat.Nat2Z.id in zmax; try lia.
      assumption. }
    rewrite nat_N_bitvector_big, Znat.Z_N_nat;[|rewrite N_len_max; simpl; lia].
    unfold nat_bitvector_big; replace (_ / _) with 0; [ reflexivity | ].
    rewrite div_small; lia.
Qed.

Theorem twos_complement_min_1s : forall {n} (b : t bool (S n)),
  b = b1 :: const b0 _ <-> opp (pow 2 (of_nat n)) = twos_complement b.
Proof.
  intros n b; rewrite (VectorSpec.eta b).
  unfold twos_complement.
  assert (bitvector_nat_big (tl b) < 2 ^ n) as L1.
  { apply bitvector_nat_big_lt_2pow. }
  rewrite twos_complement_big, Znat.nat_N_Z.
  remember (tl b) as tlb; simpl in tlb; 
  remember (hd b) as hdb; simpl in hdb; 
  clear Heqhdb Heqtlb b.
  change 2%Z with (of_nat 2).
  rewrite BinInt.Z.eq_opp_l, opp_sub_swap.
  rewrite Z_inj_pow.
  change 2%N with (N.of_nat 2).
  rewrite <- Nat2N_inj_pow.
  split; intro H.
  - injection H; intros H0 H1; apply inj_pair2 in H0; clear H.
    rewrite H1; clear H1.
    simpl bitValN; rewrite N.mul_1_l.
    rewrite Znat.nat_N_Z, <- Znat.Nat2Z.inj_sub;[|lia]. 
    f_equal.
    rewrite bitvector_fin_big_0_const in H0; lia.
  - destruct hdb.
    + f_equal.
      rewrite bitvector_fin_big_0_const.
      rewrite N.mul_1_l, Znat.nat_N_Z in H; lia.
    + rewrite N.mul_0_l in H; lia.
Qed.

Theorem twos_complement_nmin_1s : forall {n} (b : t bool (S n)),
  b <> b1 :: const b0 _ <-> (lt (opp (pow 2 (of_nat n))) (twos_complement b)).
Proof.
  intros n b.
  transitivity (opp (pow 2 (of_nat n)) <> twos_complement b).
  { apply ZifyClasses.not_morph, twos_complement_min_1s. }
  assert (le (opp (pow 2 (of_nat n))) (twos_complement b)).
  { apply twos_complement_min. }
  lia.
Qed.

(* signed bitvector arithmetic *)

(*Absolute value of signed vector*)
Definition bv_abs {n} (v : t bool (S n)) : t bool n :=
  N_bitvector_big n (Z.abs_N (twos_complement v)).

Theorem bv_abs_correct : forall {n} (v : t bool (S n)),
  lt (opp (pow 2 (of_nat n))) (twos_complement v) ->
  bv_abs v = nat_bitvector_big n (Z.abs_nat (twos_complement v)).
Proof.
  intros.
  unfold bv_abs.
  rewrite <- N_nat_bitvector_big.
  - rewrite Znat.Zabs_nat_N; reflexivity.
  - assert (lt (twos_complement v) (pow 2 (of_nat n)));[apply twos_complement_max|].
    assert (lt 0 (pow 2 (of_nat n)));[apply BinInt.Z.pow_pos_nonneg; lia|].
    replace (2 ^ n) with (to_nat (pow 2 (of_nat n)));[lia|].
    rewrite Z2_inj_pow, Znat.Nat2Z.id; try lia; auto.
Qed.

(*Negative of signed vector*)
Definition bv_neg {n} (v : t bool (S n)) : t bool (S n) :=
  twos_complement_inv n (opp (twos_complement v)).

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
Definition bv_smul {n} (v1 v2 : t bool (S n)) : t bool (S (n + n)) :=
  twos_complement_inv (n + n) 
    (mul (twos_complement v1) (twos_complement v2)).

Theorem bv_smul_correct_1 : forall {n} (v1 v2 : t bool (S n)),
  bv_smul v1 v2 = twos_complement_inv (n + n) 
    (mul (twos_complement v1) (twos_complement v2)).
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

Theorem bv_smul_correct_sign : forall {n} (v1 v2 : t bool (S n)),
  v1 <> b1 :: const b0 _ -> v2 <> b1 :: const b0 _ ->
  hd (bv_smul v1 v2) = ltb (mul (twos_complement v1) (twos_complement v2)) 0.
Proof.
  intros n v1 v2.
  rewrite bv_smul_correct_1.
  intros min1 min2.
  rewrite twos_complement_nmin_1s in min1, min2.
  remember (mul _ _) as m.
  unfold twos_complement_inv.
  destruct (ltb _ _) eqn:ltm.
  - rewrite BinInt.Z.ltb_lt in ltm.
    change 2%Z with (of_nat 2).
    rewrite BinInt.Z.add_comm, <- BinInt.Z.sub_opp_r, Z_inj_pow.
    rewrite <- (Znat.Z2Nat.id (opp m));[|lia].
    rewrite Znat.Z2N.inj_sub;[|lia].
    do 2 rewrite <- Znat.nat_N_Z, Znat.N2Z.id.
    assert (to_nat (opp m) < 2 ^ (n + n)).
    { rewrite <- Znat.Nat2Z.id, <- Znat.Z2Nat.inj_lt; try lia.
      rewrite <- Z_inj_pow, Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      rewrite <- BinInt.Z.pow_add_r, Heqm, opp_lt_swap_l, BinInt.Z.pow_add_r; try lia.
      apply lt_opp_mul_mul; try lia; apply twos_complement_max. }
    rewrite <- Nat2N.inj_sub, N_nat_bitvector_big;[|simpl; lia].
    unfold nat_bitvector_big; change (hd (?x :: _)) with x.
    replace (_ / _) with 1; [ reflexivity | ].
    symmetry; apply div_bet_1; split; simpl; lia.
  - rewrite BinInt.Z.ltb_ge in ltm.
    assert (to_nat m < 2 ^ (n + n)).
    { rewrite <- Znat.Nat2Z.id, <- Znat.Z2Nat.inj_lt; try lia.
      rewrite <- Z_inj_pow, Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      rewrite <- BinInt.Z.pow_add_r, Heqm, BinInt.Z.pow_add_r; try lia.
      apply lt_mul_mul; try lia; apply twos_complement_max. }
    assert (0 < 2 ^ (n + n));[apply zero2pow|].
    rewrite nat_N_bitvector_big;[|rewrite N_len_max, Znat.Z_N_nat; simpl; lia].
    unfold nat_bitvector_big; change (hd (?x :: _)) with x.
    replace (_ / _) with 0; [ reflexivity | ].
    symmetry; apply div_small; lia.
Qed.

Theorem smul_max : forall {n} (v1 v2 : t bool (S n)),
  le (mul (twos_complement v1) (twos_complement v2)) (pow 2 (of_nat (n + n))).
Proof.
  intros n v1 v2.
  rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
  apply le_mul_mul;
  try apply twos_complement_min; apply twos_complement_max.
Qed.

(* Computes the upper n bits of the signed multiplication
   of two two's-complement numbers.

  Output is the sign of product (in first bit) followed
  by the upper bits of the absolute-value of the product.

  This means that, for example, -1 * 1 will result in
  10...0, which is NOT representing a twos complement 
  number.
*)
Definition bv_smulh : forall {n} (v1 v2 : t bool (S n)), 
                                 t bool (S n).
  intros n v1 v2.
  apply twos_complement in v1, v2.
  remember (mul v1 v2) as v12.
  apply cons.
  - exact (ltb v12 Z0).
  - apply (fun (x : t bool (n + n)) => fst (splitat n x)), 
          N_bitvector_big, Z.abs_N, v12.
Defined.

Theorem bv_smulh_correct_value :
  forall {n} (v1 v2 : t bool (S n)), 
  lt (opp (pow 2 (of_nat n))) (twos_complement v1) ->
  lt (opp (pow 2 (of_nat n))) (twos_complement v2) ->
  tl (bv_smulh v1 v2) = 
    fst (splitat n (nat_bitvector_big (n + n) 
    (Z.abs_nat (mul (twos_complement v1) (twos_complement v2))))).
Proof. 
  intros.
  unfold bv_smulh.
  rewrite <- N_nat_bitvector_big.
  - f_equal.
    rewrite Znat.Zabs_nat_N; auto.
  - assert (lt (twos_complement v1) (pow 2 (of_nat n)));[apply twos_complement_max|].
    assert (lt (twos_complement v2) (pow 2 (of_nat n)));[apply twos_complement_max|].
    assert (lt 0 (pow 2 (of_nat n)));[apply BinInt.Z.pow_pos_nonneg; lia|].
    replace (2 ^ (n + n)) with (to_nat (mul (pow 2 (of_nat n)) (pow 2 (of_nat n)))).
    2: { rewrite PeanoNat.Nat.pow_add_r. 
         replace (2 ^ n) with (to_nat (pow 2 (of_nat n)));[lia|].
         rewrite Z2_inj_pow, Znat.Nat2Z.id; try lia.
         reflexivity. }
    rewrite Znat.Zabs2Nat.abs_nat_spec, <- Znat.Z2Nat.inj_lt; try lia.
    rewrite BinInt.Z.abs_mul.
    apply lt_mul_mul; try lia.
Qed.

Theorem bv_smulh_correct_sign :
  forall {n} (v1 v2 : t bool (S n)), 
  v1 <> b1 :: const b0 _ -> v2 <> b1 :: const b0 _ ->
  hd (bv_smulh v1 v2) = hd (bv_smul v1 v2).
Proof.
  intros n v1 v2 min1 min2; 
  rewrite twos_complement_nmin_1s in min1, min2.
  assert (lt (twos_complement v1) (pow 2 (of_nat n))).
  { apply twos_complement_max. }
  assert (lt (twos_complement v2) (pow 2 (of_nat n))).
  { apply twos_complement_max. }
  unfold bv_smulh; simpl.
  rewrite <- (twos_complement_sign (n + n)); try reflexivity;
  rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
  - apply le_opp_mul_mul; lia.
  - apply lt_mul_mul; lia.
Qed.

Definition bv_lt {n} (u v : t bool n) : bool :=
  (bitvector_N_big u <? bitvector_N_big v)%N.

Theorem bv_lt_correct {n} (u v : t bool n) :
  bv_lt u v = (bitvector_nat_big u <? bitvector_nat_big v).
Proof.
  intros.
  unfold bv_lt.
  repeat rewrite bitvector_nat_N_big.
  destruct (bitvector_nat_big u <? bitvector_nat_big v) eqn:ltV.
  - rewrite PeanoNat.Nat.ltb_lt in ltV.
    rewrite N.ltb_lt.
    lia.
  - rewrite PeanoNat.Nat.ltb_nlt in ltV.
    rewrite N.ltb_nlt.
    lia.
Qed.

Definition bv_le {n} (u v : t bool n) : bool :=
  (bitvector_N_big u <=? bitvector_N_big v)%N.

Theorem bv_le_correct {n} (u v : t bool n) :
  bv_le u v = (bitvector_nat_big u <=? bitvector_nat_big v).
Proof.
  intros.
  unfold bv_le.
  repeat rewrite bitvector_nat_N_big.
  destruct (bitvector_nat_big u <=? bitvector_nat_big v) eqn:leV.
  - rewrite PeanoNat.Nat.leb_le in leV.
    rewrite N.leb_le.
    lia.
  - rewrite PeanoNat.Nat.leb_nle in leV.
    rewrite N.leb_nle.
    lia.
Qed.

Definition bv_succ {n} (v : t bool n) := 
  (N_bitvector_big n (N.succ (bitvector_N_big v) mod 2 ^ N.of_nat n)).

Theorem bv_succ_correct : forall {n} (v : t bool n),
  bv_succ v = nat_bitvector_big n (S (bitvector_nat_big v) mod 2 ^ n).
Proof.
  intros n v.
  assert (bitvector_nat_big v < 2 ^ n);[apply bitvector_nat_big_lt_2pow|].
  unfold bv_succ.
  rewrite <- bitvector_N_nat_big, <- N2Nat.inj_succ.
  replace (2 ^ N.of_nat n)%N
     with (N.of_nat (2 ^ n));[|rewrite Nat2N_inj_pow; reflexivity].
  assert (2 ^ n <> 0);[apply PeanoNat.Nat.pow_nonzero;lia|].
  rewrite nat_N_bitvector_big, N2Nat_inj_mod.
  repeat f_equal.
  apply Nnat.Nat2N.id.
  lia.
  rewrite N_len_max, N2Nat_inj_mod, Nnat.Nat2N.id;[|lia].
  apply mod_upper_bound.
  assumption.
Qed.

Ltac pc_simpl := 
  repeat rewrite bv_succ_correct;
  repeat rewrite nat_bitvector_big_inv; try apply mod_upper_bound; try lia;
  repeat rewrite mod_small; try lia.
