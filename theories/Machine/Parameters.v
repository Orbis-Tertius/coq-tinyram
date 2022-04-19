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
  Parameter (wordSizeEighth registerCount : nat).

  (*"""  
  the word size [is] required to be a power of 2 and divisible by 8.
  """*)
  Definition wordSize := wordSizeEighth * 8.
  Parameter (wordSizeLength : nat).
  Axiom wordSizePow2 : wordSize = 2 ^ wordSizeLength.

  (*"""
  The binary encoding assumes that 6 + 2 · ceil(log_2 K) ≤ [wordSize]
  """*)
  Axiom encodingAxiom : 6 + 2 * log2_up registerCount <= wordSize.
End TinyRAMParameters.

Module TinyRAMThrms (Params : TinyRAMParameters).
  Import Params.
  Export Params.

  Theorem wordSizePos : 0 < wordSize.
  Proof.
    assert (6 + 2 * log2_up registerCount <= wordSize);
    [ exact encodingAxiom | lia ].
  Qed.

  Theorem wordSizeMin5 : 5 < wordSize.
  Proof.
    assert (6 + 2 * log2_up registerCount <= wordSize);
    [ exact encodingAxiom | lia ].
  Qed.

  Theorem wordSizeEighthPos : 0 < wordSizeEighth.
  Proof.
    assert (0 < wordSizeEighth * 8); [ apply wordSizePos | lia ].
  Qed.

  Theorem wordSizeMin8 : 8 <= wordSize.
  Proof.
    unfold wordSize.
    assert (0 < wordSizeEighth); [ apply wordSizeEighthPos | ].
    destruct wordSizeEighth; lia.
  Qed.

  Definition wordSizeEighthFin : fin (2 ^ wordSize).
    exists wordSizeEighth.
    assert (0 < wordSizeEighth * 8); [ apply wordSizePos | ].
    transitivity (wordSizeEighth * 8); [ lia | ].
    apply pow_gt_lin_r.
    lia.
  Defined.

  Theorem registerCount_lt_2powwordSize :
    registerCount <= 2 ^ wordSize.
  Proof.
    assert (6 + 2 * log2_up registerCount <= wordSize);
      [ apply encodingAxiom | ].
    destruct registerCount; [ lia | ].
    rewrite log2_up_le_pow2; lia.
  Qed.

  Theorem registerCount_lt_2powwordSize2 :
    0 < registerCount -> registerCount < 2 ^ wordSize.
  Proof.
    intro.
    rewrite log2_lt_pow2; [ | assumption ].
    apply (lt_le_trans _ (6 + 2 * log2_up registerCount));
     [ | exact encodingAxiom ].
    change (6 + ?x) with (S (5 + x)).
    apply le_n_S.
    rewrite add_comm.
    apply Plus.le_plus_trans.
    rewrite plus_n_O at 1.
    change (log2 ?x + 0) with (1 * log2 x).
    apply mul_le_mono_nonneg; try lia.
    apply le_log2_log2_up.
  Qed.

  Theorem wordSize_expand : wordSize = (wordSize - 8 + 8).
  Proof. assert (8 <= wordSize). { exact wordSizeMin8. } lia. Qed.

  Theorem address_min : 255 < 2 ^ wordSize.
  Proof.
    rewrite wordSize_expand.
    replace (wordSize - 8 + 8)
       with (8 + (wordSize - 8));[|lia].
    change (2 ^ (8 + ?x))
      with (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * 2 ^ x)))))))).
    assert (0 < 2 ^ (wordSize - 8));[apply Arith.zero2pow|].
    lia.
  Qed.

  (*"""
  increments pc (the program counter) by i [...] where
  [...] i = 2W/8 for vnTinyRAM.
  """*)
  Definition pcIncrement : nat := 2 * wordSizeEighth.

  Definition regId : Type := fin registerCount.
End TinyRAMThrms.
