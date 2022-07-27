From Coq Require Import
  Lia Nat BinPos Pnat BinNat BinIntDef
  Arith ZArith.Int Numbers.BinNums
  NArith.Nnat.
Import PeanoNat.Nat.
Require Import ProofIrrelevance.
Import EqNotations.
Import BinInt.Z(of_nat, to_nat, opp,
                sub, add, mul, pow,
                leb, le, ltb, lt).


(*Don't know where to put these.*)
Theorem rew_id : forall A (P : A -> Type) (a : A) (e : a = a) (k : P a),
  rew [fun x : A => P x] e in k = k.
Proof.
  intros A P a e k.
  replace e with (Logic.eq_refl a).
  - reflexivity.
  - apply proof_irrelevance.
Qed.

Theorem rew_f_bubble : 
  forall A (P : A -> Type) (Q : A -> Type) (f : forall x, P x -> Q x)
  (a b : A) (e : a = b) (k : P a),
  f _ (rew [fun x : A => P x] e in k) = 
  rew [fun x : A => Q x] e in (f _ k).
Proof. intros A P Q f a b []; reflexivity. Qed.

Theorem subset_eq_proj1 :
  forall {A} {P : A -> Prop} (k1 k2 : { x | P x }),
  proj1_sig k1 = proj1_sig k2 -> k1 = k2.
Proof.
  intros A P [k1 k1P] [k2 k2P].
  simpl. intros eq.
  apply subset_eq_compat.
  assumption.
Qed.

Theorem depEqLem : 
  forall (B : Type) 
         (F : B -> Type)
         (P : forall b : B, F b -> Prop)
         (b1 b2 : B) (eqb : b1 = b2)
         (p1 : F b1) (p2 : F b2),
         (rew eqb in p1 = p2) ->
         P b1 p1 ->
         P b2 p2.
Proof.
  intros B F P b1 b2 eqb.
  destruct eqb.
  intros p1 p2 eqp.
  destruct eqp.
  intros Pp.
  exact Pp.
Qed.

Theorem dep_if_true :
  forall x (P : Set)
           (t : forall (e : x = true), P)
           (f : forall (e: x = false), P)
           (eq : x = true),
  ( if x as b return (x = b -> P)
    then t
    else f ) Logic.eq_refl
  = t eq.
Proof.
  intros x P t f eq.
  destruct x.
  - f_equal; apply proof_irrelevance.
  - discriminate eq.
Qed.

Theorem dep_if_false :
  forall x (P : Set)
           (t : forall (e : x = true), P)
           (f : forall (e: x = false), P)
           (eq : x = false),
  ( if x as b return (x = b -> P)
    then t
    else f ) Logic.eq_refl
  = f eq.
Proof.
  intros x P t f eq.
  destruct x.
  - discriminate eq.
  - f_equal; apply proof_irrelevance.
Qed.

Theorem plus_reg_r : forall n m p : nat, n + p = m + p -> n = m.
Proof.
  intros n m p.
  induction p as [|p IHp].
  + repeat rewrite add_0_r; trivial.
  + repeat rewrite <- plus_n_Sm.
    intro eq.
    injection eq as eq2.
    apply IHp.
    exact eq2.
Qed.

Definition lt_sub:
  forall {n m}, n < m -> {p : nat | m = p + n /\ 0 < p}.
    intros n m.
    generalize dependent n.
    induction m as [|m IHm]; intros n lnm. 
    - destruct (nlt_0_r _ lnm).
    - destruct n as [|n].
      + exists (S m).
        lia.
      + apply Lt.lt_S_n in lnm.
        destruct (IHm n lnm).
        exists x.
        lia.
Defined.

Definition le_sub:
  forall {n m}, n <= m -> {p : nat | m = p + n /\ 0 <= p}.
  intros n m.
  generalize dependent n.
  induction m as [|m IHm]; intros n lnm. 
  - exists 0.
    lia.
  - destruct n as [|n].
    + exists (S m).
      lia.
    + apply Le.le_S_n in lnm.
      destruct (IHm n lnm).
      exists x.
      lia.
Defined.

Theorem log2_upS_Slog2 : forall x,
  x > 1 -> log2_up (S x) = S (log2 x).
Proof.
  intro x; destruct x; [ lia | ].
  reflexivity.
Qed.

Theorem log2_up_ajoint_lem : forall {x}, ~ (2 ^ x < 1).
Proof.
  intro x; induction x as [|x IHx].
  - simpl; lia.
  - intro. apply IHx. 
    transitivity (2 ^ S x); [ | assumption ].
    simpl; lia.
Qed.

(* Adjoint theorem/Galois connection defining ceiling log2 *)
Theorem log2_up_lt_pow2 : forall (x y : nat),
  (2 ^ x < y) <-> (x < log2_up y).
Proof.
  intros x y.
  destruct (0 <? y) eqn:g0y.
  - apply log2_up_lt_pow2.
    rewrite ltb_lt in g0y.
    assumption.
  - rewrite ltb_ge in g0y.
    destruct y; [ | lia ].
    split; [ lia | ].
    unfold log2_up; simpl.
    lia.
Qed.

Theorem mod_2_0or1 : forall n, (n mod 2 = 0) \/ (n mod 2 = 1).
Proof.
  intro.
  induction n as [|n IHn].
  - auto.
  - replace (S n) with (1 + n); [ | reflexivity ].
    rewrite add_mod; [ | lia ].
    destruct IHn.
    + right.
      rewrite H.
      reflexivity.
    + left.
      rewrite H.
      reflexivity.
Qed.

Theorem neq0_div_lt : forall a b c,
  b <> 0 -> a < c -> a / b < c.
Proof.
  intros.
  apply div_lt_upper_bound; [ assumption | ].
  apply (lt_le_trans _ c); [ assumption | ].
  destruct (Mult.mult_O_le c b).
  + destruct (H H1).
  + exact H1.
Qed.

Theorem add_sub_distr: forall n m p : nat, 
  p <= m -> m <= n -> 
  n - (m - p) = n - m + p.
Proof.
  intros n m p lpm lmpn.
  apply add_sub_eq_r.
  rewrite <- add_assoc.
  rewrite le_plus_minus_r; [ | assumption ].
  rewrite sub_add; trivial.
Qed.

Theorem div_bet_1 : 
  forall {n m}, m <= n < 2 * m -> n / m = 1.
Proof.
  intros n m [lmn ln2m].
  assert (m <> 0); [ lia | ].
  apply (div_le_mono _ _ _ H) in lmn.
  rewrite div_same in lmn; [ | lia ].
  rewrite mul_comm in ln2m.
  apply (div_lt_upper_bound _ _ _ H) in ln2m.
  lia.
Qed.

Theorem zero2pow : forall n, 0 < 2 ^ n.
Proof.
  destruct n. { simpl; lia. }
  change 0 with (0 ^ S n); apply pow_lt_mono_l; lia.
Qed.

Theorem opp_sub_swap : forall n m, opp (sub n m) = sub m n.
Proof.
  intros n m.
  rewrite <- BinInt.Z.opp_involutive.
  repeat rewrite BinInt.Z.opp_sub_distr.
  rewrite BinInt.Z.opp_add_distr.
  rewrite BinInt.Z.opp_involutive.
  rewrite BinInt.Z.add_comm.
  reflexivity.
Qed.

Theorem negb_inj : forall x y, negb x = negb y -> x = y.
Proof.
  destruct x, y; trivial; simpl; intro H; discriminate H.
Qed.

Theorem Z_ltb_lt : forall n m : Z, (ltb n m) = true <-> lt n m.
Proof.
  intros n m; split.
  - destruct n, m; intro H; unfold ltb in H; simpl in H; try lia;
    unfold lt; simpl; destruct (BinPos.Pos.compare _ _); trivial;
    discriminate H.
  - destruct n, m; intro H; unfold ltb; simpl; try lia;
    unfold lt in H; simpl in H; destruct (BinPos.Pos.compare _ _); trivial;
    discriminate H.
Qed.

Theorem Z_leb_le : forall n m : Z, (leb n m) = true <-> le n m.
Proof.
  intros n m; split.
  - destruct n, m; intro H; unfold leb in H; simpl in H; try lia;
    unfold le; simpl; destruct (BinPos.Pos.compare _ _); trivial;
    try discriminate H; intro H2; discriminate H2.
  - destruct n, m; intro H; unfold leb; simpl; try lia;
    unfold le in H; simpl in H;
    repeat destruct (BinPos.Pos.compare _ _); simpl; trivial;
    try discriminate H; destruct (H (Logic.eq_refl _)).
Qed.

Theorem Z_nltb_ge : forall n m : Z, (ltb n m) = false <-> le m n.
Proof.
  intros n m.
  transitivity ((leb m n) = true). 2: { apply Z_leb_le. }
  split; intro; apply negb_inj.
  - rewrite <- BinInt.Z.ltb_antisym.
    exact H.
  - rewrite <- BinInt.Z.leb_antisym.
    exact H.
Qed.

Theorem Z_nleb_gt : forall n m : Z, (leb n m) = false <-> lt m n.
Proof.
  intros n m.
  transitivity ((ltb m n) = true). 2: { apply Z_ltb_lt. }
  split; intro; apply negb_inj.
  - rewrite <- BinInt.Z.leb_antisym.
    exact H.
  - rewrite <- BinInt.Z.ltb_antisym.
    exact H.
Qed.

Theorem opp_le_swap_r: forall n m : Z, le n (opp m) <-> le m (opp n).
Proof.
  intros n m.
  rewrite <- (BinInt.Z.opp_involutive n) at 1.
  rewrite <- BinInt.Z.opp_le_mono.
  reflexivity.
Qed.

Theorem opp_le_swap_l: forall n m : Z, le (opp n) m <-> le (opp m) n.
Proof.
  intros n m.
  rewrite <- (BinInt.Z.opp_involutive m) at 1.
  rewrite <- BinInt.Z.opp_le_mono.
  reflexivity.
Qed.

Theorem opp_lt_swap_l: forall n m : Z, lt (opp n) m <-> lt (opp m) n.
Proof.
  intros n m.
  rewrite <- (BinInt.Z.opp_involutive m) at 1.
  rewrite <- BinInt.Z.opp_lt_mono.
  reflexivity.
Qed.

Theorem Z_inj_pow : forall x y, 
  pow (of_nat x) (of_nat y) = of_nat (x ^ y).
Proof.
  intros x y.
  induction y.
  - reflexivity.
  - rewrite Znat.Nat2Z.inj_succ, BinInt.Z.pow_succ_r.
    2: { apply Zorder.Zle_0_nat. }
    rewrite IHy.
    simpl; rewrite Znat.Nat2Z.inj_mul.
    reflexivity.
Qed.

Theorem Z2_inj_pow : forall x y, 
  le Z0 x -> le Z0 y ->
  to_nat (pow x y) = to_nat x ^ to_nat y.
Proof.
  intros x y l0x l0y.
  rewrite <- (Znat.Z2Nat.id x), <- (Znat.Z2Nat.id y) at 1; try assumption.
  rewrite Z_inj_pow, Znat.Nat2Z.id.
  reflexivity.
Qed.

Theorem le_opp_intro_l : forall n m,
  le Z0 n ->
  le m Z0 ->
  le n m -> le (opp m) n.
Proof. intros n m npos mneg lnm; lia. Qed.

Theorem le_opp_elim_l : forall n m,
  le Z0 m ->
  le n Z0 ->
  le (opp m) n -> le n m.
Proof. intros n m npos mneg lnm; lia. Qed.

Theorem le_opp_intro_r : forall n m,
  le Z0 n ->
  le m Z0 ->
  le n m -> le m (opp n).
Proof. intros n m npos mneg lnm; lia. Qed.

Theorem le_opp_elim_r : forall n m,
  le Z0 m ->
  le n Z0 ->
  le m (opp n) -> le n m.
Proof. intros n m npos mneg lnm; lia. Qed.

Theorem le_opp_mul_mul : forall p1 p2 t1 t2,
  le (opp p1) t1 -> le (opp p2) t2 -> 
  lt t1 p1 -> lt t2 p2 ->
  le (opp (mul p1 p2)) (mul t1 t2).
Proof.
  intros.
  assert (lt Z0 p1); [ lia | ].
  assert (lt Z0 p2); [ lia | ].
  destruct (ltb t1 Z0) eqn:zt1; 
  destruct (ltb t2 Z0) eqn:zt2;
  try rewrite Z_ltb_lt in zt1;
  try rewrite Z_ltb_lt in zt2;
  try rewrite Z_nltb_ge in zt1;
  try rewrite Z_nltb_ge in zt2;
  try lia.
  - rewrite opp_le_swap_l, <- BinInt.Z.mul_opp_l.
    apply BinInt.Z.mul_le_mono_nonneg; lia.
  - rewrite opp_le_swap_l, <- BinInt.Z.mul_opp_r.
    apply BinInt.Z.mul_le_mono_nonneg; lia.
Qed.

Theorem lt_opp_mul_mul : forall p1 p2 t1 t2,
  lt (opp p1) t1 -> lt (opp p2) t2 -> 
  lt t1 p1 -> lt t2 p2 ->
  lt (opp (mul p1 p2)) (mul t1 t2).
Proof.
  intros.
  assert (lt Z0 p1); [ lia | ].
  assert (lt Z0 p2); [ lia | ].
  destruct (ltb t1 Z0) eqn:zt1; 
  destruct (ltb t2 Z0) eqn:zt2;
  try rewrite Z_ltb_lt in zt1;
  try rewrite Z_ltb_lt in zt2;
  try rewrite Z_nltb_ge in zt1;
  try rewrite Z_nltb_ge in zt2;
  try lia.
  - rewrite opp_lt_swap_l, <- BinInt.Z.mul_opp_l.
    apply BinInt.Z.mul_lt_mono_nonneg; lia.
  - rewrite opp_lt_swap_l, <- BinInt.Z.mul_opp_r.
    apply BinInt.Z.mul_lt_mono_nonneg; lia.
Qed.

Theorem lt_mul_mul : forall p1 p2 t1 t2,
  lt (opp p1) t1 -> lt (opp p2) t2 -> 
  lt t1 p1 -> lt t2 p2 ->
  lt (mul t1 t2) (mul p1 p2).
Proof. 
  intros.
  assert (lt Z0 p1); [ lia | ].
  assert (lt Z0 p2); [ lia | ].
  destruct (ltb t1 Z0) eqn:zt1; 
  destruct (ltb t2 Z0) eqn:zt2;
  try rewrite Z_ltb_lt in zt1;
  try rewrite Z_ltb_lt in zt2;
  try rewrite Z_nltb_ge in zt1;
  try rewrite Z_nltb_ge in zt2;
  try lia.
  - rewrite <- BinInt.Z.mul_opp_opp.
    apply BinInt.Z.mul_lt_mono_nonneg; lia.
  - apply BinInt.Z.mul_lt_mono_nonneg; try lia.
Qed.

Theorem le_mul_mul : forall p1 p2 t1 t2,
  le (opp p1) t1 -> le (opp p2) t2 -> 
  lt t1 p1 -> lt t2 p2 ->
  le (mul t1 t2) (mul p1 p2).
Proof. 
  intros.
  assert (lt Z0 p1); [ lia | ].
  assert (lt Z0 p2); [ lia | ].
  destruct (ltb t1 Z0) eqn:zt1; 
  destruct (ltb t2 Z0) eqn:zt2;
  try rewrite Z_ltb_lt in zt1;
  try rewrite Z_ltb_lt in zt2;
  try rewrite Z_nltb_ge in zt1;
  try rewrite Z_nltb_ge in zt2;
  try lia.
  - rewrite <- BinInt.Z.mul_opp_opp.
    apply BinInt.Z.mul_le_mono_nonneg; lia.
  - apply BinInt.Z.mul_le_mono_nonneg; try lia.
Qed.

(* Some binary nat theorems which aren't present in 
   the Coq version that ITrees likes. *)

Theorem Nat2N_inj_pow:
  forall n n' : nat,
  N.of_nat (n ^ n') =
  (N.of_nat n ^ N.of_nat n')%N.
Proof.
  intros.
  generalize dependent n.
  induction n';[reflexivity|].
  intro.
  rewrite Nnat.Nat2N.inj_succ.
  rewrite N.pow_succ_r'.
  rewrite <- IHn'.
  rewrite PeanoNat.Nat.pow_succ_r'.
  apply Nnat.Nat2N.inj_mul.
Qed.

Theorem N2Nat_inj_pow:
  forall n n' : N,
  N.to_nat (n ^ n') =
  (N.to_nat n ^ N.to_nat n').
Proof.
  intros.
  rewrite <- Nat2N.id.
  rewrite Nat2N_inj_pow. 
  repeat rewrite N2Nat.id.
  reflexivity.
Qed.

Lemma inj_compare a a' :
 (a ?= a')%N = (N.to_nat a ?= N.to_nat a').
Proof.
 destruct a as [|p], a' as [|p']; simpl; trivial.
 - now destruct (Pos2Nat.is_succ p') as (n,->).
 - now destruct (Pos2Nat.is_succ p) as (n,->).
 - apply Pos2Nat.inj_compare.
Qed.

Theorem N2Nat_inj_mod n n' :
  n' <> N0 ->
  N.to_nat (n mod n') =
  (N.to_nat n mod N.to_nat n').
Proof.
  intros.
  destruct n' as [|n']; [now destruct n|].
  apply PeanoNat.Nat.mod_unique
   with (N.to_nat (n / (N.pos n'))).
  - apply PeanoNat.Nat.compare_lt_iff.
    rewrite <- inj_compare.
    apply N.mod_lt.
    intro H0; discriminate H0.
  - now rewrite <- N2Nat.inj_mul, <- N2Nat.inj_add, <- N.div_mod.
Qed.

Theorem Nat2N_inj_mod:
  forall n n' : nat,
  n' <> 0 ->
  N.of_nat (n mod n') =
  (N.of_nat n mod N.of_nat n')%N.
Proof.
  intros.
  apply N2Nat.inj.
  rewrite N2Nat_inj_mod;[|lia].
  now repeat rewrite Nat2N.id.
Qed.

Theorem N2Nat_inj_div n n' :
  n' <> N0 ->
  N.to_nat (n / n') =
  (N.to_nat n / N.to_nat n').
Proof.
  intros.
  destruct n' as [|n']; [now destruct n|].
  apply PeanoNat.Nat.div_unique
  with (N.to_nat (n mod (N.pos n'))).
  - apply PeanoNat.Nat.compare_lt_iff.
    rewrite <- inj_compare.
    apply N.mod_lt; lia.
  - now rewrite <- N2Nat.inj_mul, <- N2Nat.inj_add, <- N.div_mod.
Qed.

Theorem Nat2N_inj_div:
  forall n n' : nat,
  n' <> 0 ->
  N.of_nat (n / n') =
  (N.of_nat n / N.of_nat n')%N.
Proof.
  intros.
  apply N2Nat.inj.
  rewrite N2Nat_inj_div;[|lia].
  now repeat rewrite Nat2N.id.
Qed.

Theorem N2Nat_inj_lt:
  forall n m : N, (n < m)%N <-> (N.to_nat n < N.to_nat m)%nat.
Proof.
 destruct n as [|p], m as [|p']; simpl.
 - split.
   + intro H.
     apply (N.lt_irrefl _) in H.
     contradiction.
   + intro H.
     apply (lt_irrefl _) in H.
     contradiction.
 - destruct (Pos2Nat.is_succ p') as (n,->).
   split.
   + intro H.
     apply lt_0_succ.
   + intro H.
     now apply (N.ltb_lt 0 (N.pos p')).
 - destruct (Pos2Nat.is_succ p) as (n,->).
   split.
   + intro H.
     apply (N.ltb_lt (N.pos p) 0) in H.
     inversion H.
   + intro H.
     apply (ltb_lt (S n) 0) in H.
     inversion H.
 - apply Pos2Nat.inj_lt.
Qed.

Theorem N2Nat_inj_le:
  forall n m : N, (n <= m)%N <-> (N.to_nat n <= N.to_nat m)%nat.
Proof.
 destruct n as [|p], m as [|p']; simpl.
 - split.
   + intro H.
     apply le_refl.
   + intro H.
     apply N.le_refl.
 - destruct (Pos2Nat.is_succ p') as (n,->).
   split.
   + intro H.
     apply le_0_l.
   + intro H.
     now apply (N.leb_le 0 (N.pos p')).
 - destruct (Pos2Nat.is_succ p) as (n,->).
   split.
   + intro H.
     apply (N.leb_le (N.pos p) 0) in H.
     inversion H.
   + intro H.
     apply (leb_le (S n) 0) in H.
     inversion H.
 - apply Pos2Nat.inj_le.
Qed.

Theorem mod_2_div : forall k, k mod 2 = 0 -> k / 2 = S k / 2.
Proof.
  assert (forall k,
            (k mod 2 = 0 -> k / 2 = S k / 2) /\
            (k mod 2 = 1 -> S k / 2 = S (S k) / 2));[|
  intro k; destruct (H k); assumption].
  induction k;[simpl;lia|destruct IHk];
  split; intro.
  - apply H0.
    change k with (0 + k).
    rewrite <- H1 at 1.
    rewrite PeanoNat.Nat.add_mod_idemp_l;[|lia].
    replace (S k + k) with (1 + 2 * k);[|lia].
    rewrite <- PeanoNat.Nat.add_mod_idemp_r;[|lia].
    rewrite PeanoNat.Nat.mul_comm, PeanoNat.Nat.mod_mul;simpl;lia.
  - assert (forall k, S (S k) / 2 = S (k / 2));[
        intro k2;change (S (S k2)) with (1 * 2 + k2);
        rewrite PeanoNat.Nat.div_add_l; lia|].
    repeat rewrite H2.
    f_equal.
    apply H.
    change (S k) with (1 + k) in H1.
    replace 0 with ((2 + k) mod 2) at 2;[|
      replace (2 + k) with (1 + (1 + k));[|lia];
      rewrite <- PeanoNat.Nat.add_mod_idemp_r, H1;
      simpl; lia].
    rewrite <- PeanoNat.Nat.add_mod_idemp_l; simpl; lia.
Qed.

Theorem nmod_2_0 : forall k, k mod 2 <> 0 -> k mod 2 = 1.
Proof.
  assert (forall k,
            (k mod 2 <> 0 -> k mod 2 = 1) /\
            (k mod 2 <> 1 -> k mod 2 = 0));[|
  intro k; destruct (H k); assumption].
  induction k;[simpl;lia|destruct IHk];
  split; intro;
  change (S k) with (1 + k);
  rewrite <- PeanoNat.Nat.add_mod_idemp_r;
  try lia.
  - rewrite H0;[reflexivity|].
    intro.
    change (S k) with (1 + k) in H1.
    rewrite <- PeanoNat.Nat.add_mod_idemp_r in H1.
    rewrite H2 in H1; simpl in H1.
    all: lia.
  - rewrite H;[reflexivity|].
    intro.
    change (S k) with (1 + k) in H1.
    rewrite <- PeanoNat.Nat.add_mod_idemp_r in H1.
    rewrite H2 in H1; simpl in H1.
    all: lia.
Qed.

