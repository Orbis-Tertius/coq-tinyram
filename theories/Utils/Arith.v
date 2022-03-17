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