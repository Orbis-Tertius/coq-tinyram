From Coq Require Import
  Arith
  Lia.
Import PeanoNat.Nat.
Require Import ProofIrrelevance.
Import EqNotations.


(*Don't know where to put this.*)
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
  intro x; destruct x. { lia. }
  reflexivity.
Qed.

Theorem log2_up_ajoint_lem : forall {x}, ~ (2 ^ x < 1).
Proof.
  intro x; induction x as [|x IHx].
  - simpl; lia.
  - intro. apply IHx. 
    transitivity (2 ^ S x). 2: { assumption. }
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
    destruct y. 2: { lia. }
    split. { lia. }
    unfold log2_up; simpl.
    lia.
Qed.

Theorem mod_2_0or1 : forall n, (n mod 2 = 0) \/ (n mod 2 = 1).
Proof.
  intro.
  induction n as [|n IHn].
  - auto.
  - replace (S n) with (1 + n). 2: { reflexivity. }
    rewrite add_mod. 2: { lia. }
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
  apply div_lt_upper_bound. { assumption. }
  apply (lt_le_trans _ c). { assumption. }
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
  rewrite le_plus_minus_r. 2: { assumption. }
  rewrite sub_add; trivial.
Qed.

Theorem div_bet_1 : 
  forall {n m}, m <= n < 2 * m -> n / m = 1.
Proof.
  intros n m [lmn ln2m].
  assert (m <> 0). { lia. }
  apply (div_le_mono _ _ _ H) in lmn.
  rewrite div_same in lmn. 2: { lia. }
  rewrite mul_comm in ln2m.
  apply (div_lt_upper_bound _ _ _ H) in ln2m.
  lia.
Qed.
