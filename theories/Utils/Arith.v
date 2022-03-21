From Coq Require Import
  Lia.
Import PeanoNat.Nat.

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

