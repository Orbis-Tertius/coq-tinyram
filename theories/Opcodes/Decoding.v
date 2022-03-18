From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Vectors.
From TinyRAM.Utils Require Import
  BitVectors.
From TinyRAM.Utils Require Import
  Fin.
Import PeanoNat.Nat.
From TinyRAM.Machine Require Import
  Parameters.
From TinyRAM.Machine Require Import
  Words.

Module TinyRAMState (Params : TinyRAMParameters).
  Module TRWords := TinyRAMWords Params.
  Import TRWords.

  Theorem interpSplitLem : 
    wordSize =
      5 + 1 + (log2 registerCount) + (log2 registerCount) +
      (wordSize - 6 - 2 * log2 registerCount).
    assert (6 + 2 * log2 registerCount <= wordSize).
    { apply encodingAxiom. }
    lia.
  Qed.

  Definition interpSplit : Word ->
    (*"""
    Field #1. This field stores the instruction's opcode,
              which consists of 5 = ceil(log2 29) bits.
    """*)
    Vector.t bool 5 * 
    (*"""
    Field #2. This field is a bit that is 0 if A is a
              register name and 1 if A is an immediate value.
    """*)
    bool * 
    (*"""
    Field #3. This field stores a register name operand, which consists
              of ceil(log2 [registerCount]) bits. It is all 0's when not
              used. This is the name of the instruction's destination
              register (i.e. the one to be modified) if any.
    """*)
    Vector.t bool (log2 registerCount) *
    (*"""
    Field #4. This field stores a register name operand, which consists
              of ceil(log2 [registerCount]) bits. It is all 0's when not
              used. This is the name of a register operand (if any) that
              will *not* be modified by the instruction.
    """*)
    Vector.t bool (log2 registerCount) *
    (*"""
    Field #5. This field consists of padding with any sequence of 
              W - 6 - 2|K| bits, so that the first five fields fit exactly
              in a string of W bits.
    """*)
    Vector.t bool (wordSize - 6 - 2 * log2 registerCount).
    intro w.
    unfold Word in w.
    rewrite interpSplitLem in w.
    apply Vector.splitat in w; destruct w as [w f5].
    split. 2: { exact f5. }
    apply Vector.splitat in w; destruct w as [w f4].
    split. 2: { exact f4. }
    apply Vector.splitat in w; destruct w as [w f3].
    split. 2: { exact f3. }
    apply Vector.splitat in w; destruct w as [f1 f2].
    split. { exact f1. }
    destruct (vector_cons_split f2) as [b _].
    exact b.
  Defined.













    (*"""
    Field #6. This is either the name of another register (which is not
              modified by the instruction) or an immediate value, as
              determined by field #2. The length of this field is W bits
              (which is the maximum between the length of a register name
              and of an immediate value).
    """*)
    Vector.t bool wordSize.




(*"""

• 
• 
"""*)