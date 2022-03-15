From Coq Require Import
  Lia
  String.
From ExtLib Require Import
  RelDec.
From ExtLib.Data Require Import
  String
  Map.FMapAList.
From ITree Require Import
  ITree.
From TinyRAM.Redo Require Import
  Vectors.
From TinyRAM.Utils Require Import
  Fin.

(* 
  Note: Text between triple quotes are
  direct quotes from the TinyRAM 2.000 spec.
*)

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
  Axiom wordSizePow2 : wordSize = Nat.pow 2 wordSizeLength.

  (*Axiom (H0 : exists k, wordSize = 4 * k).
  Axiom H1 : 6 + 2 * Nat.log2 registerCount <= wordSize.
  Axiom H2 : 0 < wordSize. (* for MSB *)
  Definition memorySize : nat := Nat.pow 2 wordSize.
  Definition incrAmount : nat := Nat.div wordSize 4.*)
End TinyRAMParameters.

Module TinyRAMTypes (Params : TinyRAMParameters).
  Import Params.
  Export Params.

  (*"""
  each register consists of [wordSize] bits
  """*)
  Definition Register := Vector.t bool wordSize.

  Definition Byte := Vector.t bool 8.

  (*Registers can be cleanly split into bytes.*) 
  Definition RegisterBytes :
    forall (r:Register), 
    exists (v : Vector.t Byte wordSizeEighth), 
    vector_length_coerce wordSizeDiv8 r = vector_concat v.
  intros r.
  remember (vector_length_coerce wordSizeDiv8 r) as r8.
  exists (vector_unconcat r8).
  rewrite vector_concat_inv1.
  reflexivity.
  Defined.

  """
  Memory, which is a linear array of 2^[wordSize] bytes.
  """


  Record MachineState : Type :=
    mkMachineState {
        (*"""
        The program counter, denoted pc; it consists of [wordSize] bits.
        """*)
        programCounter : Register;
        (*"""
        [registerCount] general-purpose registers, [...]
        """*)
        registerValues : Vector.t Register registerCount;
        (*conditionFlag : Flag;*)
        (*memoryValues : alist Address Word;*)
        (*primaryInput : InputTape primary;*)
        (*auxiliaryInput : InputTape auxiliary;*)
      }.


"""
The (condition) flag [...]; it consists of a single bit.
"""



"""
When storing or loading blocks of multiple bytes, we use the little-endian convention 
(i.e., the least-significant byte is at the lowest address). 

We say that a block is aligned to the A-th byte if its least-significant byte is at address A.
"""