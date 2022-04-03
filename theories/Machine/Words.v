From Coq Require Import
  Lia VectorEq.
From TinyRAM.Utils Require Import
  Vectors.
From TinyRAM.Utils Require Import
  BitVectors.
From TinyRAM.Utils Require Import
  Fin.
From TinyRAM.Machine Require Import
  Parameters.
Import PeanoNat.Nat.

Module TinyRAMWords (Params : TinyRAMParameters).
  Import Params.
  Export Params.

  (*"""
  each Word consists of [wordSize] bits
  """*)
  Definition Word := Vector.t bool wordSize.

  Definition wcast (v : Word) := 
    cast v (eq_sym (succ_pred_pos _ wordSizePos)).

  (*Registers can be cleanly split into bytes.*) 
  Definition WordBytes (r : Word) : 
    Vector.t Byte wordSizeEighth :=
    vector_unconcat r.

  Definition BytesWord (v : Vector.t Byte wordSizeEighth) : Word 
    := vector_concat v.

  Theorem WordBytesIso1 :
    forall (r : Word), 
    BytesWord (WordBytes r) = r.
  Proof.
    intros r.
    unfold WordBytes, BytesWord.
    rewrite vector_concat_inv1.
    reflexivity.
  Qed.

  Theorem WordBytesIso2 :
    forall (v : Vector.t Byte wordSizeEighth), 
    WordBytes (BytesWord v) = v.
  Proof.
    intros r.
    unfold WordBytes, BytesWord.
    rewrite vector_concat_inv2.
    reflexivity.
  Qed.

End TinyRAMWords.


