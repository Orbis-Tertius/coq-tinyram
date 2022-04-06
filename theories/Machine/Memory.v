From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Vectors.
From TinyRAM.Utils Require Import
  BitVectors.
From TinyRAM.Utils Require Import
  Fin.
From TinyRAM.Machine Require Import
  Parameters.
From TinyRAM.Machine Require Import
  Words.
Import PeanoNat.Nat.

Module TinyRAMMem (Params : TinyRAMParameters).
  Module TRWords := TinyRAMWords Params.
  Import TRWords.
  Export TRWords.

  (*"""
  Memory, which is a linear array of 2^[wordSize] bytes.
  """*)
  Definition Memory := Vector.t Byte (2 ^ wordSize).

  (*"""
  We say that a block is aligned to the A-th byte if its
  least-significant byte is at address A.
  """*)

  (*"""
  When storing or loading blocks of multiple bytes, 
  [...] the least-significant byte is at the lowest address.
  """*)
  Definition Memory_Block_Load
    (m : Memory)
    (idx blksz : fin (2 ^ wordSize)) :
    Vector.t Byte (proj1_sig blksz) :=
    Vector.rev (Block_Load m idx blksz).

  (*"""
  When storing or loading blocks of multiple bytes, 
  [...] the least-significant byte is at the lowest address.
  """*)
  Definition Memory_Block_Store 
    (m : Memory)
    (idx blksz : fin (2 ^ wordSize))
    (block : Vector.t Byte (proj1_sig blksz)) :
    Memory :=
    Block_Store m idx blksz (Vector.rev block).

  (* Since a Word is a memory block, it can be loaded as well. *)
  Definition Memory_Word_Load
    (m : Memory)
    (idx : fin (2 ^ wordSize)) :
    Word.
    unfold Word.
    apply vector_concat.
    apply (Memory_Block_Load m idx wordSizeEighthFin).
  Defined.

  (* Since a Word is a memory block, it can be stored as well. *)
  Definition Memory_Word_Store 
    (m : Memory)
    (idx : fin (2 ^ wordSize))
    (reg : Word) :
    Memory.
    apply (Memory_Block_Store m idx wordSizeEighthFin).
    apply vector_unconcat, reg.
  Defined.

  Definition Register_Index (w : Word) : fin (2 ^ wordSize) :=
    bitvector_fin_big w.

  Definition Memory_Word_Load_from_Reg 
    (m : Memory) (idx : Word) : Word :=
    Memory_Word_Load m (Register_Index idx).

  Definition Memory_Word_Store_from_Reg 
    (m : Memory) (idx reg : Word) : Memory :=
    Memory_Word_Store m (Register_Index idx) reg.

End TinyRAMMem.


