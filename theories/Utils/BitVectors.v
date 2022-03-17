From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Fin.
From TinyRAM.Utils Require Import
  Vectors.
From TinyRAM.Utils Require Import
  Arith.
Import PeanoNat.Nat.

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

Definition bv_add : forall {n} (b1 b2 : Vector.t bool n), Vector.t bool n.
  intros n b1 b2.
  apply fin_bitvector; apply bitvector_fin in b1, b2.
  destruct b1 as [b1 b1prp]; destruct b2 as [b2 b2prp].
  exists ((b1 + b2) mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.



Definition bv_incr : forall {n}, Vector.t bool n -> nat -> Vector.t bool n.
  intros n b i.
  apply fin_bitvector; apply bitvector_fin in b.
  destruct b as [b bprp].
  exists ((b + i) mod (2 ^ n)).
  apply mod_upper_bound.
  lia.
Defined.

