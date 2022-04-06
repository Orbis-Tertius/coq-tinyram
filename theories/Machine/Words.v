From Coq Require Import
  Lia VectorEq.
From TinyRAM.Utils Require Import
  Vectors BitVectors Fin.
From TinyRAM.Machine Require Import
  Parameters.
Import PeanoNat.Nat.

Module TinyRAMWords (Params : TinyRAMParameters).
  Module TRThrms := TinyRAMThrms Params.
  Import TRThrms.
  Export TRThrms.

  (*"""
  each Word consists of [wordSize] bits
  """*)
  Definition Word := Vector.t bool wordSize.

  Definition wcast (v : Word) := 
    cast v (eq_sym (succ_pred_pos _ wordSizePos)).

  Definition wuncast (v : Vector.t bool (S (pred wordSize))) :=
    cast v (succ_pred_pos _ wordSizePos).

  Definition wbcast {A} (v : Vector.t A wordSize) :
                        Vector.t A (wordSize - 8 + 8).
    assert (8 <= wordSize). { exact wordSizeMin8. }
    replace (_ + _) with wordSize. { exact v. }
    lia.
  Defined.

  Definition wbuncast {A} (v : Vector.t A (wordSize - 8 + 8)) :
                          Vector.t A wordSize.
    assert (8 <= wordSize). { exact wordSizeMin8. }
    replace (_ + _) with wordSize in v. { exact v. }
    lia.
  Defined.

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

  Definition Address : Type := fin (2 ^ wordSize).
  Definition Register : Type := fin registerCount.
End TinyRAMWords.
