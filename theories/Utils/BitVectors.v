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

