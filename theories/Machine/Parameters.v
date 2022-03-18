From Coq Require Import
  Lia.
Import PeanoNat.Nat.
From TinyRAM.Utils Require Import
  Fin.

Module Type TinyRAMParameters.
  (*"""  
  TinyRAM [...] is parametrized by two integers: the word size [...]
  and the number of registers [...]
  """*)
  Parameter (wordSize registerCount : nat).

  (*"""  
  the word size [is] required to be a power of 2 and divisible by 8.
  """*)
  Parameter (wordSizeLength wordSizeEighth : nat).
  Axiom wordSizeDiv8 : wordSize = wordSizeEighth * 8.
  Axiom wordSizePow2 : wordSize = 2 ^ wordSizeLength.

  (*"""
  The binary encoding assumes that 6 + 2 · ceil(log_2 K) ≤ [wordSize]
  """*)
  Axiom encodingAxiom : 6 + 2 * log2 registerCount <= wordSize.

  (* ??? *)
  Axiom wordSizePos : 0 < wordSize. (* for MSB *)

  Theorem wordSizeEighthPos : 0 < wordSizeEighth.
  Proof.
    assert (0 < wordSizeEighth * 8).
    { rewrite <- wordSizeDiv8. apply wordSizePos. }
    lia.
  Qed.

  Definition wordSizeEighthFin : fin (2 ^ wordSize).
    exists wordSizeEighth.
    assert (0 < wordSizeEighth * 8).
    { rewrite <- wordSizeDiv8. apply wordSizePos. }
    transitivity (wordSizeEighth * 8).
    { lia. }
    rewrite <- wordSizeDiv8.
    apply pow_gt_lin_r.
    lia.
  Defined.

  (*"""
  increments pc (the program counter) by i [...] where
  [...] i = 2W/8 for vnTinyRAM.
  """*)
  Definition pcIncrement : nat := 2 * wordSizeEighth.

  Definition regId : Type := fin registerCount.
End TinyRAMParameters.
