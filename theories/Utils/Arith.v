From Coq Require Import
  Lia.
Import PeanoNat.Nat.

Definition lt_sub:
  forall {n m}, n < m -> {p : nat | m = p + n /\ 0 < p}.
  Proof.  
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
  Proof.  
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

(* Ceiling log base 2 function *)
Definition clog2 (x : nat) : nat := 
  match x with
  | 0 => 0
  | S 0 => 0
  | S (S n) => S (log2 (S n))
  end.

Theorem clog2S_Slog2 : forall x,
  x > 1 -> clog2 (S x) = S (log2 x).
Proof.
  intro x; destruct x. { lia. }
  destruct x. { lia. }
  reflexivity.
Qed.

Theorem clog2_ajoint_lem : forall {x}, ~ (2 ^ x < 1).
Proof.
  intro x; induction x as [|x IHx].
  - simpl; lia.
  - intro. apply IHx. 
    transitivity (2 ^ S x). 2: { assumption. }
    simpl; lia.
Qed.

(* Adjoint theorem/Galois connection defining ceiling log2 *)
Theorem clog2_lt_pow2 : forall (x y : nat),
  (2 ^ x < y) <-> (x < clog2 y).
  intros x y.
Proof.
  split; intro.
  - destruct (1 <? y) eqn:g1y.
    + rewrite ltb_lt in g1y.
      destruct y. { lia. } destruct y. { lia. }
      simpl; rewrite lt_succ_r.
      rewrite <- log2_le_pow2; lia.
    + rewrite ltb_nlt in g1y.
      assert (y = 1) as y1. { lia. }
      rewrite y1 in H.
      destruct (clog2_ajoint_lem H).
  - destruct (1 <? y) eqn:g1y.
    + rewrite ltb_lt in g1y.
      destruct y. { lia. }
      rewrite lt_succ_r.
      rewrite log2_le_pow2. 2: { lia. }
      rewrite <- lt_succ_r.
      destruct y. { lia. }
      exact H.
    + rewrite ltb_nlt in g1y.
      assert (y <= 1). { lia. }
      destruct (y =? 0) eqn:g0y.
      * rewrite eqb_eq in g0y.
        rewrite g0y in H.
        simpl in H; lia.
      * rewrite eqb_neq in g0y.
        assert (y = 1) as y1. { lia. }
        rewrite y1 in H.
        simpl in H; lia.
Qed.
